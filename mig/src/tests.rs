// SPDX-License-Identifier: MIT
use super::*;
use std::ops::RangeBounds;
use std::path::Path;

mod driver;

use driver::TestDriver;

fn load_migrations(path: impl AsRef<Path>) -> MigrationSet {
    eprintln!("Loading migrations from {}", path.as_ref().display());
    let mut migrations = MigrationSet::new();
    for path in std::fs::read_dir(path).expect("Failed to read migrations directory") {
        let entry = path.expect("Failed to read migrations directory entry");
        let filename = entry.file_name().into_string().expect("Invalid filename");
        let content = std::fs::read_to_string(entry.path()).expect("Failed to read file");

        migrations
            .add_migration_from_filename(filename.as_str(), content.as_str())
            .expect("Failed to add migration");
    }
    migrations
}

fn run_test(
    source: &str,
    range: impl RangeBounds<usize>,
    expected_end: Option<usize>,
    transactional: bool,
    alt_tag: bool,
    result: Result<&str, (&str, &str)>,
) {
    fn extract_bound(bound: std::ops::Bound<&usize>) -> Option<usize> {
        match bound {
            std::ops::Bound::Included(value) => Some(*value),
            std::ops::Bound::Excluded(value) => Some(*value),
            std::ops::Bound::Unbounded => None,
        }
    }

    let migrations = load_migrations(source);

    let start = extract_bound(range.start_bound()).unwrap_or(0);
    let end = extract_bound(range.end_bound())
        .or_else(|| migrations.migrations().last().map(|v| v.id));

    let expected_end = expected_end
        .or(end)
        .or_else(|| migrations.migrations().last().map(|v| v.id))
        .unwrap_or(start);

    eprintln!("Transactional: {transactional}");

    let mut driver = TestDriver::new(transactional, start);
    if alt_tag {
        driver.tag = "alt";
    }

    let actual_result = migrations.migrate_to(&mut driver, end);
    match (actual_result, result) {
        (Ok(()), Ok(expected)) => {
            assert_eq!(driver.lines, expected);
            assert_eq!(driver.version, expected_end);
        }
        (Ok(()), Err(expected)) => {
            panic!("Expected error: {:?}", expected.1);
        }
        (Err(e), Ok(_)) => {
            panic!("Unexpected error: {e}");
        }
        (Err(e), Err((r2, e2))) => {
            assert_eq!(e.to_string(), e2);
            assert_eq!(r2, driver.lines);
            assert_eq!(driver.version, expected_end);
        }
    }
}
macro_rules! define_test {
    ($name:ident ($($spec:tt),*) = $source:literal [$($start:literal)? .. $($end:literal)?] $(($actual_end:literal))? => $expected:literal $(/ $err:literal)? ) => {
        #[test]
        fn $name () {
            let range = $($start)? .. $($end)?;
            let expected_end = None$(.or(Some($actual_end)))?;
            let transactional = define_test!(@check txn $($spec)*);
            let alt_tag = define_test!(@check alt $($spec)*);
            run_test($source, range, expected_end, transactional, alt_tag,
                Ok($expected)
                $(.and_then(|exp| Err((exp, $err))))?
            );
        }
    };

    (@check txn txn $($x:tt)*) => {true};
    (@check alt alt $($x:tt)*) => {true};
    (@check $target:tt) => {false};
    (@check $target:tt $nop:tt $($v:tt)*) => {define_test!(@check $target $($v)*)};
}

// I don't like this syntax, but I can't be bothered to figure out how to do it better.
// Contributions are welcome.
define_test!(simple() = "src/tests/simple"[..] => "ace");
define_test!(tagsel(alt) = "src/tests/simple"[..] => "bce");
define_test!(partial() = "src/tests/simple"[..1] => "ac");
define_test!(error() = "src/tests/error"[..](0) => "acgihd!r" / "Migration 2.1 failed (err) but rolled back successfully");
// Note that rollback tests do not reset the version number, so the version number is the highest successful migration.
define_test!(error_tx(txn) = "src/tests/error"[..](1) => "acg!r" / "Migration 2.1 failed (err) but rolled back successfully");
