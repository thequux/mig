// SPDX-License-Identifier: MIT
use std::ops::{Deref, DerefMut};
use async_trait::async_trait;
use mig::{AsyncDriver, AsyncExecutor, TransactionTerminatedError};

/// PostgresQL migration driver
///
/// This uses the driver tag "`postgres`"
pub struct AsyncPostgresDriver<T: Deref<Target = tokio_postgres::Client> + DerefMut + Send> {
    pub conn: T,
}

impl<T: Deref<Target = tokio_postgres::Client> + DerefMut + Send> AsyncPostgresDriver<T> {
    pub fn new(conn: T) -> Self {
        Self { conn }
    }
}

#[async_trait]
impl<T: Deref<Target = tokio_postgres::Client> + DerefMut + Send> AsyncDriver
for AsyncPostgresDriver<T>
{
    fn db_type(&self) -> &'static str {
        "postgres"
    }

    fn has_transactional_ddl(&self) -> bool {
        true
    }

    async fn prepare_db(&mut self) -> Result<usize, anyhow::Error> {
        let mut exec = self.start_migration().await?;
        let state = exec.get_migration_state().await?;
        exec.commit().await?;
        Ok(state)
    }

    async fn start_migration<'a>(
        &'a mut self,
    ) -> Result<Box<dyn AsyncExecutor + Send + 'a>, anyhow::Error> {
        let txn = self.conn.transaction().await?;
        txn.execute(
            "CREATE TABLE IF NOT EXISTS migration_state(meta_id integer primary key, meta_ival integer)",
            &[],
        ).await?;
        let state = txn.query_one(
            "INSERT INTO migration_state(meta_id, meta_int) VALUES(1, 0) ON CONFLICT(meta_id) UPDATE SET meta_int = migration_state.meta_int RETURNING meta_ival",
            &[]).await
            .map(|row| row.get::<_, u32>("meta_ival") as usize)
            .map_err(anyhow::Error::from)?;

        Ok(Box::new(AsyncPostgresExecutor {
            txn: Some(txn),
            state,
        }))
    }
}

pub struct AsyncPostgresExecutor<'a> {
    txn: Option<tokio_postgres::Transaction<'a>>,
    state: usize,
}

impl<'txn> AsyncPostgresExecutor<'txn> {
    pub fn txn<'a>(
        &'a mut self,
    ) -> Result<&'a mut tokio_postgres::Transaction<'txn>, TransactionTerminatedError> {
        self.txn.as_mut().ok_or(TransactionTerminatedError)
    }

    pub fn take_txn(
        &mut self,
    ) -> Result<tokio_postgres::Transaction<'txn>, TransactionTerminatedError> {
        self.txn.take().ok_or(TransactionTerminatedError)
    }
}

#[async_trait]
impl AsyncExecutor for AsyncPostgresExecutor<'_> {
    async fn execute(&mut self, sql: &str) -> Result<(), anyhow::Error> {
        self.txn()?.simple_query(sql).await?;
        Ok(())
    }

    async fn commit(&mut self) -> Result<(), anyhow::Error> {
        self.take_txn()?.commit().await?;
        Ok(())
    }

    async fn rollback(&mut self) -> Result<(), anyhow::Error> {
        self.take_txn()?.rollback().await?;
        Ok(())
    }

    async fn set_migration_state(&mut self, migration_id: usize) -> Result<(), anyhow::Error> {
        self.txn()?
            .execute(
                "UPDATE migration_state SET meta_int = $1 WHERE meta_id = 1",
                &[&(migration_id as u32)],
            )
            .await?;
        self.state = migration_id;
        Ok(())
    }

    async fn get_migration_state(&mut self) -> Result<usize, anyhow::Error> {
        Ok(self.state)
    }
}
