// SPDX-License-Identifier: MIT
//! # Database Migrations
//! Migrations will normally be loaded from SQL files, which contain normal SQL
//! statements separated by migration directives.
//!
//! Each directive must be on its own line and must be prefixed with `--: `.
//! The following directives are supported:
//!
//! * `up` - The SQL statements to run when applying the migration.
//! * `down` - The SQL statements to run when reverting the migration.
//! * `section` - Begin a new section of SQL statements.
//!
//! `up` and `down` directives can also include a list of database types that
//! they support, like so:
//!
//! ```sql
//! --: up sqlite,postgres
//! CREATE TABLE foo (
//!     id INTEGER PRIMARY KEY,
//!     name TEXT NOT NULL
//! );
//! ```
//!
//! When applying a migration to a database type not listed in the directive,
//! the migration will be skipped. If no database type is listed, the migration
//! will be applied to all databases mentioned in the section or to all
//! databases if no directive specifies a database type.
//!
//! If a section has an `up` directive that applies to the chosen database but
//! does not include any `down` statements for that database, the migration
//! will be considered irreversible. If the `up` sections fail, the migration
//! will *not* be rolled back. Otherwise, the `down` statements will be run in
//! forward order.
//!
//! Sections can be used to group related SQL statements and their down
//! directives. When rolling back a migration, the sections will be rolled back
//! in reverse order. Note, however, that the down statements *within* a section
//! are applied in forward order
//!
//! ## Example
//!
//! ```sql
//! --: up sqlite
//! CREATE TABLE foo (
//!     id INTEGER PRIMARY KEY,
//!     name TEXT NOT NULL
//! );
//!
//! --: up postgres
//! CREATE TABLE foo (
//!     id SERIAL PRIMARY KEY,
//!     name TEXT NOT NULL
//! );
//!
//! --: down
//! DROP TABLE foo;
//!
//! --: section
//! --: up
//! ALTER TABLE foo DROP COLUMN name;
//!
//! --: section
//! --: up
//! ALTER TABLE foo ADD GOLLUM age INTEGER;
//!
//! --: down
//! ALTER TABLE foo DROP COLUMN IF EXISTS age;
//! ```
//!
//! The first section of the migration will be applied to SQLite and Postgres,
//! but not to MySQL; the type of the id column will depend on the database. If
//! it fails, the down sections will be applied to roll back the migration. If
//! this section is rolled back on MySQL, nothing will happen, as previous
//! directives mentioned postgresql and sqlite.
//!
//! The second section will be applied to all databases, even MySQL: type limits
//! are considered per-section. If it fails, the migration will halt without
//! rolling back. The error will be reported for operator intervention.
//!
//! The third section will be applied to all databases, but due to the syntax
//! error, it will fail on all reasonable databases. This will cause the down
//! migration to be applied. The engine will then attempt to roll back the
//! second section and finally the first section, but as the second section is
//! irreversible, the migration will be halted and the situation left for
//! operator intervention.
//!
//! # Transactional DDL
//! Some databases, such as PostgreSQL, support transactional DDL. For these
//! databases, rollback works differently. When a migration fails, the entire
//! transaction is rolled back.
#![allow(unused)]

use std::borrow::Cow;
use async_trait::async_trait;
use std::collections::{BTreeMap, HashSet};
use std::error::Error;
use std::ops::{Deref, DerefMut, Not};
use std::pin::Pin;
use std::result;
use std::task::Poll;
use thiserror::Error;
use crate::MigrationError::RollbackFailed;

pub mod sources;

// This is only used for the sync adaptor
fn fake_await<T: Future>(f: Pin<&mut T>) -> T::Output {
    use std::future::Future;
    let mut fake_ctx = std::task::Context::from_waker(std::task::Waker::noop());
    match f.poll(&mut fake_ctx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("fake_await called on a future that is not ready"),
    }
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid directive: {0}")]
    InvalidDirective(String),
    #[error("Duplicate migration: {0}")]
    DuplicateMigration(usize),
    #[error("Invalid filename: {0}")]
    InvalidFilename(String),
    #[error("Unable to enumerate migrations: {0}")]
    LoadError(#[source] anyhow::Error)
}

#[derive(Error, Debug)]
#[error("Migration is irreversible")]
pub struct IrreversibleMigrationError;

#[derive(Error, Debug)]
#[error("Transaction is already terminated")]
pub struct TransactionTerminatedError;

#[derive(Error, Debug)]
pub enum MigrationError {
    #[error("Migration {migration}.{section} failed: {cause}")]
    MigrationAborted {
        migration: usize,
        section: usize,
        #[source]
        cause: anyhow::Error,
    },
    #[error("Rollback of migration {migration}.{section} failed: {cause}")]
    RollbackFailed {
        migration: usize,
        section: usize,
        #[source]
        cause: anyhow::Error,
    },
    #[error("Migration {migration}.{section} failed ({cause}) but rolled back successfully")]
    MigrationRolledBack {
        migration: usize,
        section: usize,
        #[source]
        cause: anyhow::Error,
    },
    #[error(
        "Migration {forward_migration}.{forward_section} failed: {forward_cause}. Additionally, the rollback failed at {rollback_migration}.{rollback_section}: {rollback_cause}"
    )]
    MigrationAndRollbackFailed {
        forward_migration: usize,
        forward_section: usize,
        rollback_migration: usize,
        rollback_section: usize,
        #[source]
        forward_cause: anyhow::Error,
        rollback_cause: anyhow::Error,
    },
    #[error("Migration failed to start: {0}")]
    TransactionFailed(#[source] anyhow::Error),
}

impl MigrationError {
    /// Returns true if this error comes from a rollback
    pub fn is_rollback(&self) -> bool {
        !matches!(
            self,
            Self::TransactionFailed { .. } | Self::MigrationAborted { .. }
        )
    }

    fn take_cause(self) -> anyhow::Error {
        match self {
            Self::MigrationAborted { cause, .. } => cause,
            Self::RollbackFailed { cause, .. } => cause,
            Self::MigrationRolledBack { cause, .. } => cause,
            myself => myself.into(),
        }
    }

    /// Combine the error from a forward migration with the result of a rollback
    pub fn with_rollback(self, rollback: Option<MigrationError>) -> MigrationError {
        if let Self::MigrationAborted {
            migration,
            section,
            cause,
        } = self
        {
            match rollback {
                None => Self::MigrationRolledBack {
                    migration,
                    section,
                    cause,
                },
                Some(MigrationError::RollbackFailed {
                         migration: rollback_migration,
                         section: rollback_section,
                         cause: rollback_cause,
                     }) => Self::MigrationAndRollbackFailed {
                    forward_migration: migration,
                    forward_section: section,
                    rollback_migration,
                    rollback_section,
                    forward_cause: cause,
                    rollback_cause,
                },
                Some(err) => {
                    let (rollback_migration, rollback_section) =
                        err.failed_step().unwrap_or((migration, section));
                    Self::MigrationAndRollbackFailed {
                        forward_migration: migration,
                        forward_section: section,
                        forward_cause: cause,
                        rollback_migration,
                        rollback_section,
                        rollback_cause: err.take_cause(),
                    }
                }
            }
        } else {
            self
        }
    }

    pub fn failed_step(&self) -> Option<(usize, usize)> {
        match self {
            Self::MigrationAborted {
                migration, section, ..
            } => Some((*migration, *section)),
            Self::RollbackFailed {
                migration, section, ..
            } => Some((*migration, *section)),
            Self::MigrationRolledBack {
                migration, section, ..
            } => Some((*migration, *section)),
            Self::MigrationAndRollbackFailed {
                forward_migration,
                forward_section,
                ..
            } => Some((*forward_migration, *forward_section)),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BlockType {
    Up,
    Down,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScriptBlock {
    pub block_type: BlockType,
    pub db_types: HashSet<String>,
    pub statements: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub db_types: HashSet<String>,
    pub blocks: Vec<ScriptBlock>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Migration {
    pub id: usize,
    pub name: String,
    pub script: Vec<Section>,
}

/// This is the entry point for the migration engine.
#[derive(Debug)]
pub struct MigrationSet {
    migrations: BTreeMap<usize, Migration>,
}

impl ScriptBlock {
    fn applies_to(&self, tag: &str) -> bool {
        self.db_types.is_empty() || self.db_types.contains(tag)
    }
}

impl Migration {
    pub fn parse(id: usize, name: String, script: &str) -> Result<Migration, ParseError> {
        let mut block_type = BlockType::Up;
        let mut block_lines = vec![];
        let mut db_types = HashSet::new();

        let mut migration = Migration {
            id,
            name,
            script: vec![],
        };

        let mut cur_section = Section {
            db_types: HashSet::new(),
            blocks: vec![],
        };

        for line in script.lines() {
            if let Some(directive) = line.strip_prefix("--: ") {
                cur_section.blocks.push(ScriptBlock {
                    block_type,
                    db_types,
                    statements: block_lines.join("\n").trim().to_string(),
                });
                block_lines = vec![];

                let mut words = directive.split_whitespace();
                let directive = words
                    .next()
                    .ok_or(ParseError::InvalidDirective("blank directive".to_string()))?;
                match directive {
                    "up" => {
                        block_type = BlockType::Up;
                        db_types = words
                            .next()
                            .unwrap_or("")
                            .split(',')
                            .filter(|s| !s.is_empty())
                            .map(|s| s.to_string())
                            .collect();
                    }
                    "down" => {
                        block_type = BlockType::Down;
                        db_types = words
                            .next()
                            .unwrap_or("")
                            .split(',')
                            .filter(|s| !s.is_empty())
                            .map(|s| s.to_string())
                            .collect();
                    }
                    "section" => {
                        migration.script.push(cur_section);
                        cur_section = Section {
                            db_types: HashSet::new(),
                            blocks: vec![],
                        };
                        block_type = BlockType::Up;
                        db_types = HashSet::new();
                    }
                    other => {
                        return Err(ParseError::InvalidDirective(format!(
                            "invalid directive: {directive}"
                        )));
                    }
                }
            } else {
                block_lines.push(line);
            }
        }

        // Commit the last block
        cur_section.blocks.push(ScriptBlock {
            block_type,
            db_types,
            statements: block_lines.join("\n").trim().to_string(),
        });
        migration.script.push(cur_section);

        // Update the supported db types for each section
        for section in &mut migration.script {
            for block in &section.blocks {
                section.db_types.extend(block.db_types.iter().cloned());
            }
            for block in &mut section.blocks {
                if block.db_types.is_empty() {
                    block.db_types = section.db_types.clone();
                }
            }
        }

        Ok(migration)
    }
}

struct SectionIter<'a> {
    range: std::collections::btree_map::Range<'a, usize, Migration>,
    current: Option<&'a Migration>,
    step: usize,
    reverse: bool,
    emit_state: Option<usize>,
}

enum IterResult<'a> {
    SetState(usize),
    Section(usize, usize, &'a Section),
}

impl<'a> Iterator for SectionIter<'a> {
    type Item = IterResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(state) = self.emit_state.take() {
            return Some(IterResult::SetState(state));
        }
        if self.current.is_none() {
            self.current = if self.reverse {
                self.range.next_back().map(|(_, v)| v)
            } else {
                self.range.next().map(|(_, v)| v)
            };
            if let Some(current) = self.current {
                // allow setting the step to USIZE_MAX to run all sections
                if self.step > current.script.len() - 1 {
                    self.step = current.script.len() - 1;
                }
            } else {
                return None;
            }
        }

        let current = self.current.unwrap();
        let item = IterResult::Section(current.id, self.step, &current.script[self.step]);

        // advance to the next section
        if self.reverse {
            if self.step == 0 {
                self.current = self.range.next_back().map(|(_, v)| v);
                self.step = self.current.map(|v| v.script.len() - 1).unwrap_or(0);
                self.emit_state = Some(self.current.map(|v| v.id).unwrap_or(0));
            } else {
                self.step -= 1;
            }
        } else if self.step == current.script.len() - 1 {
            self.current = self.range.next().map(|(_, v)| v);
            self.emit_state = Some(current.id);
            self.step = 0;
        } else {
            self.step += 1;
        }
        Some(item)
    }
}

impl Default for MigrationSet {
    fn default() -> Self {
        Self::new()
    }
}

impl MigrationSet {
    pub fn new() -> Self {
        Self {
            migrations: BTreeMap::new(),
        }
    }

    pub fn load_from(source: impl Iterator<Item=anyhow::Result<(Cow<'static, str>, Cow<'static, [u8]>)>>) -> Result<Self, ParseError> {
        let mut migrations = Self::new();
        for item in source {
            let (name, content) = item.map_err(ParseError::LoadError)?;
            let content = std::str::from_utf8(&content).map_err(Into::into).map_err(ParseError::LoadError)?;
            migrations.add_migration_from_filename(&name, content)?;
        }
        Ok(migrations)
    }

    pub fn add_migration(&mut self, migration: Migration) -> result::Result<(), ParseError> {
        let id = migration.id;
        let old = self.migrations.insert(id, migration);
        if old.is_some() {
            Err(ParseError::DuplicateMigration(id))
        } else {
            Ok(())
        }
    }

    pub fn add_migration_from_str(
        &mut self,
        id: usize,
        name: String,
        script: &str,
    ) -> result::Result<(), ParseError> {
        let migration = Migration::parse(id, name, script)?;
        self.add_migration(migration)
    }

    pub fn add_migration_from_filename(
        &mut self,
        name: &str,
        script: &str,
    ) -> result::Result<(), ParseError> {
        let (id, name) = name
            .rsplit_once('.')
            .map_or(name, |(name, _)| name)
            .split_once(['_', '-'])
            .and_then(|(id, name)| id.parse::<usize>().ok().map(|id| (id, name.to_string())))
            .ok_or_else(|| ParseError::InvalidFilename(name.to_string()))?;
        self.add_migration_from_str(id, name, script)
    }

    /// Returns an iterator over all of the migrations in the set, in order by ID
    /// It is guaranteed that this supports efficient seeking, fetching the last element, and
    pub fn migrations(&self) -> impl Iterator<Item=&Migration> + DoubleEndedIterator {
        self.migrations.values()
    }

    async fn migrate_internal(
        &self,
        tag: &str,
        exec: &mut dyn AsyncExecutor,
        start: usize,
        end: usize,
        step: Option<usize>,
    ) -> Result<(), MigrationError> {
        eprintln!("Migrating from {}.{:?} to {}", start, step, end);
        let (start, end, reverse) = if start > end {
            (end+1, start, true)
        } else if start == end {
            return Ok(());
        } else {
            (start + 1, end, false)
        };

        let target_block_type = if reverse {
            BlockType::Down
        } else {
            BlockType::Up
        };

        let iter = SectionIter {
            range: self.migrations.range(start..=end),
            current: None,
            step: step.or(reverse.then_some(usize::MAX)).unwrap_or(0),
            emit_state: None,
            reverse,
        };
        for action in iter {
            let (mig, sec, section) = match action {
                IterResult::SetState(state) => {
                    exec.set_migration_state(state).await
                        .map_err(|e| if reverse {
                            MigrationError::MigrationAborted {
                                migration: state,
                                section: 0,
                                cause: e,
                            }
                        } else {
                            RollbackFailed {
                                migration: state + 1,
                                section: 0,
                                cause: e,
                            }
                        })?;
                    continue;
                }
                IterResult::Section(mig, sec, section) => (mig, sec, section),
            };

            eprintln!("Applying {} migration {}.{}", if reverse {"down"} else { "up" }, mig, sec);
            if !section.db_types.contains(tag) && !section.db_types.is_empty() {
                continue;
            }

            // check for irreversible sections if this is a rollback
            if reverse
                && !section.blocks.iter().any(|b| {
                b.block_type == BlockType::Down
                    && (b.db_types.is_empty() || b.db_types.contains(tag))
            })
            {
                return Err(MigrationError::RollbackFailed {
                    migration: mig,
                    section: sec,
                    cause: IrreversibleMigrationError.into(),
                });
            }

            for block in &section.blocks {
                if block.block_type != target_block_type {
                    continue;
                }
                if block.db_types.is_empty() || block.db_types.contains(tag) {
                    exec.execute(&block.statements).await.map_err(|e| {
                        if reverse {
                            MigrationError::RollbackFailed {
                                migration: mig,
                                section: sec,
                                cause: e,
                            }
                        } else {
                            MigrationError::MigrationAborted {
                                migration: mig,
                                section: sec,
                                cause: e,
                            }
                        }
                    })?;
                }
            }
        }
        Ok(())
    }

    pub fn migrate_to(
        &self,
        driver: &mut dyn SyncDriver,
        target: Option<usize>,
    ) -> Result<(), MigrationError> {
        let mut driver = SyncDriverAdapter { driver };
        let fut = self.migrate_to_async(&mut driver, target);
        fake_await(std::pin::pin!(fut))
    }

    /// Attempt to apply migrations to the database to achieve the target version. If the target
    /// version is not specified, apply all migrations.
    pub async fn migrate_to_async(
        &self,
        driver: &mut dyn AsyncDriver,
        target: Option<usize>,
    ) -> Result<(), MigrationError> {
        let has_transactional_ddl = driver.has_transactional_ddl();
        let db_tag = driver.db_type();
        let mut executor = driver
            .start_migration()
            .await
            .map_err(MigrationError::TransactionFailed)?;
        let start = executor
            .get_migration_state()
            .await
            .map_err(MigrationError::TransactionFailed)?;
        let mut target = target
            .or_else(|| self.migrations.last_key_value().map(|(id, _)| *id))
            .unwrap_or(start);

        // TODO: all this error handling is a bit ugly. Replace it with a combinator on MigrationError
        match self
            .migrate_internal(db_tag, &mut *executor, start, target, None)
            .await
        {
            Ok(()) => executor
                .commit()
                .await
                .map_err(MigrationError::TransactionFailed),
            Err(err @ MigrationError::TransactionFailed(..)) => Err(err),
            Err(err) if err.is_rollback() => {
                let _ = executor.rollback().await;
                Err(err)
            }
            Err(err) if has_transactional_ddl => Err(err.with_rollback(
                executor
                    .rollback()
                    .await
                    .err()
                    .map(MigrationError::TransactionFailed),
            )),
            Err(err) => {
                // Forward migration failed. Attempt rollback.
                let (migration, section) = err.failed_step().unwrap();
                let rollback_error = self
                    .migrate_internal(db_tag, &mut *executor, migration, start, Some(section))
                    .await
                    .err();
                let _ = executor.rollback().await;
                Err(err.with_rollback(rollback_error))
            }
        }
    }
}

pub trait SyncExecutor {
    /// Execute a chunk of SQL
    fn execute(&mut self, sql: &str) -> Result<(), anyhow::Error>;
    /// Commit the transaction
    fn commit(&mut self) -> Result<(), anyhow::Error>;
    /// Roll back the transaction
    fn rollback(&mut self) -> Result<(), anyhow::Error>;
    /// Update the migration state to indicate that the migration has been applied
    fn set_migration_state(&mut self, migration_id: usize) -> Result<(), anyhow::Error>;
    /// Get the current migration state
    fn get_migration_state(&mut self) -> Result<usize, anyhow::Error>;
}

pub trait SyncDriver {
    /// The tag that represents this driver in up and down directives
    fn db_type(&self) -> &'static str;

    /// Whether this driver supports transactional DDL
    fn has_transactional_ddl(&self) -> bool;

    /// Prepare the database for migrations. This will likely involve creating
    /// a table to track migrations.
    ///
    /// Returns the identifier of the highest migration that has been applied.
    fn prepare_db(&mut self) -> Result<usize, anyhow::Error>;

    /// Start a migration session. This will likely involve starting a transaction.
    ///
    /// Returns an executor that can be used to execute SQL statements.
    fn start_migration<'a>(
        &'a mut self,
    ) -> Result<Box<dyn SyncExecutor + Send + 'a>, anyhow::Error>;
}

#[async_trait]
pub trait AsyncExecutor {
    /// Execute a chunk of SQL
    async fn execute(&mut self, sql: &str) -> Result<(), anyhow::Error>;
    /// Commit the transaction
    async fn commit(&mut self) -> Result<(), anyhow::Error>;
    /// Roll back the transaction
    async fn rollback(&mut self) -> Result<(), anyhow::Error>;
    /// Update the migration state to indicate that the migration has been applied
    async fn set_migration_state(&mut self, migration_id: usize) -> Result<(), anyhow::Error>;
    /// Get the current migration state
    async fn get_migration_state(&mut self) -> Result<usize, anyhow::Error>;
}

#[async_trait]
pub trait AsyncDriver {
    /// The tag that represents this driver in up and down directives
    fn db_type(&self) -> &'static str;

    /// Whether this driver supports transactional DDL
    fn has_transactional_ddl(&self) -> bool;

    /// Prepare the database for migrations. This will likely involve creating
    /// a table to track migrations.
    ///
    /// Returns the identifier of the highest migration that has been applied.
    async fn prepare_db(&mut self) -> Result<usize, anyhow::Error>;

    /// Start a migration session. This will likely involve starting a transaction.
    ///
    /// Returns an executor that can be used to execute SQL statements.
    async fn start_migration<'a>(
        &'a mut self,
    ) -> Result<Box<dyn AsyncExecutor + Send + 'a>, anyhow::Error>;
}


struct SyncDriverAdapter<'a, T: SyncDriver + ?Sized> {
    driver: &'a mut T,
}

impl<'x, T: SyncDriver + ?Sized> AsyncDriver for SyncDriverAdapter<'x, T> {
    fn db_type(&self) -> &'static str {
        self.driver.db_type()
    }

    fn has_transactional_ddl(&self) -> bool {
        self.driver.has_transactional_ddl()
    }

    fn prepare_db<'a, 'async_trait>(
        &'a mut self,
    ) -> Pin<Box<dyn Future<Output=Result<usize, anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'a: 'async_trait,
    {
        Box::pin(std::future::ready(self.driver.prepare_db()))
    }

    fn start_migration<'a, 'tr>(
        &'a mut self,
    ) -> Pin<
        Box<
            dyn Future<Output=Result<Box<dyn AsyncExecutor + Send + 'a>, anyhow::Error>>
            + Send
            + 'tr,
        >,
    >
    where
        Self: 'a,
        'a: 'tr,
    {
        let executor = self.driver.start_migration().map(|executor| {
            Box::new(SyncExecutorAdapter(executor)) as Box<dyn AsyncExecutor + Send + 'a>
        });
        Box::pin(std::future::ready(executor))
    }
}

struct SyncExecutorAdapter<'a>(Box<dyn SyncExecutor + Send + 'a>);

impl<'a> AsyncExecutor for SyncExecutorAdapter<'a> {
    fn execute<'life0, 'life1, 'async_trait>(
        &'life0 mut self,
        sql: &'life1 str,
    ) -> Pin<Box<dyn Future<Output=Result<(), anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'life0: 'async_trait,
        'life1: 'async_trait,
    {
        Box::pin(std::future::ready(self.0.execute(sql)))
    }
    fn commit<'life0, 'async_trait>(
        &'life0 mut self,
    ) -> Pin<Box<dyn Future<Output=Result<(), anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'life0: 'async_trait,
    {
        Box::pin(std::future::ready(self.0.commit()))
    }
    fn rollback<'life0, 'async_trait>(
        &'life0 mut self,
    ) -> Pin<Box<dyn Future<Output=Result<(), anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'life0: 'async_trait,
    {
        Box::pin(std::future::ready(self.0.rollback()))
    }
    fn set_migration_state<'life0, 'async_trait>(
        &'life0 mut self,
        migration_id: usize,
    ) -> Pin<Box<dyn Future<Output=Result<(), anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'life0: 'async_trait,
    {
        Box::pin(std::future::ready(self.0.set_migration_state(migration_id)))
    }
    fn get_migration_state<'life0, 'async_trait>(
        &'life0 mut self,
    ) -> Pin<Box<dyn Future<Output=Result<usize, anyhow::Error>> + Send + 'async_trait>>
    where
        Self: 'async_trait,
        'life0: 'async_trait,
    {
        Box::pin(std::future::ready(self.0.get_migration_state()))
    }
}

#[cfg(test)]
mod tests;
