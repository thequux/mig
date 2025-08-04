use crate::*;

#[derive(Debug)]
pub struct TestDriver {
    transactional: bool,
    pub tag: &'static str,
    pub version: usize,
    pub pre_txn: Option<(usize, String)>,
    pub lines: String,
}

impl TestDriver {
    pub fn new(transactional: bool, version: usize) -> Self {
        Self {
            tag: "test",
            transactional,
            version,
            pre_txn: None,
            lines: String::new(),
        }
    }
}

impl SyncDriver for TestDriver {
    fn db_type(&self) -> &'static str {
        self.tag
    }

    fn has_transactional_ddl(&self) -> bool {
        self.transactional
    }

    fn prepare_db(&mut self) -> Result<usize, anyhow::Error> {
        Ok(self.version)
    }

    fn start_migration<'a>(
        &'a mut self,
    ) -> Result<Box<dyn SyncExecutor + Send + 'a>, anyhow::Error> {
        if self.pre_txn.is_some() {
            return Err(anyhow::Error::msg("already in a transaction"));
        }
        self.pre_txn = Some((self.version, self.lines.clone()));
        Ok(Box::new(self))
    }
}

impl SyncExecutor for &mut TestDriver {
    fn execute(&mut self, sql: &str) -> Result<(), anyhow::Error> {
        eprintln!("execute({sql:?})");
        if let Some(err) = sql.strip_prefix('!') {
            Err(anyhow::Error::msg(err.to_owned()))
        } else {
            self.lines += sql;
            Ok(())
        }
    }

    fn commit(&mut self) -> Result<(), anyhow::Error> {
        eprintln!("commit()");
        anyhow::ensure!(self.pre_txn.is_some(), "not in a transaction");
        self.pre_txn = None;
        Ok(())
    }

    fn rollback(&mut self) -> Result<(), anyhow::Error> {
        eprintln!("rollback()");
        self.lines += "!r";
        Ok(())
    }

    fn set_migration_state(&mut self, migration_id: usize) -> Result<(), anyhow::Error> {
        eprintln!("set_migration_state({migration_id})");
        self.version = migration_id;
        Ok(())
    }

    fn get_migration_state(&mut self) -> Result<usize, anyhow::Error> {
        Ok(self.version)
    }
}
