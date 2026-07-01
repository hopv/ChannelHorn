use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use channel_rust_impl::{chc::Setting, parser};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SolverResult {
    Sat,
    Unsat,
    Timeout,
}

impl SolverResult {
    fn as_str(self) -> &'static str {
        match self {
            SolverResult::Sat => "sat",
            SolverResult::Unsat => "unsat",
            SolverResult::Timeout => "timeout",
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Solver {
    Hoice,
    Z3,
}

impl Solver {
    fn name(self) -> &'static str {
        match self {
            Solver::Hoice => "hoice",
            Solver::Z3 => "z3",
        }
    }

    fn run(self, out_dir: &Path, chc_path: &Path) -> std::io::Result<Output> {
        match self {
            Solver::Hoice => run_hoice(out_dir, chc_path),
            Solver::Z3 => run_z3(chc_path),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct SolverOverride {
    file_name: &'static str,
    solver: Solver,
}

#[test]
fn sat_benchmarks_are_sat() {
    run_benchmarks(
        "tests/bench/sat",
        &[SolverResult::Sat],
        &["optional"],
        Solver::Hoice,
        &[
            SolverOverride {
                file_name: "ack.txt",
                solver: Solver::Z3,
            },
            SolverOverride {
                file_name: "calc_server.txt",
                solver: Solver::Z3,
            },
        ],
    );
}

#[test]
fn unsat_benchmarks_are_unsat() {
    run_benchmarks(
        "tests/bench/unsat",
        &[SolverResult::Unsat],
        &[],
        Solver::Z3,
        &[],
    );
}

fn run_benchmarks(
    root: &str,
    expected: &[SolverResult],
    excluded_dirs: &[&str],
    default_solver: Solver,
    solver_overrides: &[SolverOverride],
) {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = manifest_dir.join(root);
    let mut cases = collect_files(&root, excluded_dirs);
    cases.sort();

    if let Ok(filter) = env::var("CHC_BENCH_FILTER") {
        cases.retain(|case| case.to_string_lossy().contains(&filter));
    }

    assert!(
        !cases.is_empty(),
        "no benchmark files found under {}",
        root.display()
    );

    let mut failures = Vec::new();
    for case in cases {
        let solver = solver_for_case(&case, default_solver, solver_overrides);
        if let Err(failure) = run_benchmark(manifest_dir, &case, expected, solver) {
            failures.push(failure);
        }
    }

    assert!(
        failures.is_empty(),
        "{} benchmark failure(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

fn solver_for_case(case: &Path, default_solver: Solver, overrides: &[SolverOverride]) -> Solver {
    let Some(file_name) = case.file_name().and_then(|name| name.to_str()) else {
        return default_solver;
    };

    overrides
        .iter()
        .find(|override_| override_.file_name == file_name)
        .map(|override_| override_.solver)
        .unwrap_or(default_solver)
}

fn collect_files(root: &Path, excluded_dirs: &[&str]) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_files_inner(root, excluded_dirs, &mut files);
    files
}

fn collect_files_inner(dir: &Path, excluded_dirs: &[&str], files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap_or_else(|err| {
        panic!(
            "failed to read benchmark directory {}: {err}",
            dir.display()
        )
    }) {
        let entry = entry.unwrap_or_else(|err| {
            panic!(
                "failed to read benchmark directory entry in {}: {err}",
                dir.display()
            )
        });
        let path = entry.path();
        let file_type = entry
            .file_type()
            .unwrap_or_else(|err| panic!("failed to read file type for {}: {err}", path.display()));

        if file_type.is_dir() {
            let dir_name = entry.file_name();
            let dir_name = dir_name.to_string_lossy();
            if !excluded_dirs.contains(&dir_name.as_ref()) {
                collect_files_inner(&path, excluded_dirs, files);
            }
        } else if file_type.is_file() {
            files.push(path);
        }
    }
}

fn run_benchmark(
    manifest_dir: &Path,
    benchmark_path: &Path,
    expected: &[SolverResult],
    solver: Solver,
) -> Result<(), String> {
    let rel_path = benchmark_path
        .strip_prefix(manifest_dir)
        .unwrap_or(benchmark_path);
    let rel_path = rel_path.display().to_string();
    let input = fs::read_to_string(benchmark_path)
        .map_err(|err| format!("{rel_path}: failed to read benchmark: {err}"))?;
    let program = parser::parse_program(&input)
        .map_err(|err| format!("{rel_path}: failed to parse benchmark: {err}"))?;
    let chc = program
        .lower_to_chc(Setting {
            no_timestamps: false,
        })
        .map_err(|err| format!("{rel_path}: failed to lower benchmark to CHC: {err}"))?;

    let temp_dir = env::temp_dir().join(format!(
        "channel_rust_impl_chc_bench_{}",
        std::process::id()
    ));
    fs::create_dir_all(&temp_dir)
        .map_err(|err| format!("{rel_path}: failed to create temp directory: {err}"))?;
    let safe_name = sanitize_path(&rel_path);
    let chc_path = temp_dir.join(format!("{safe_name}.smt2"));
    fs::write(&chc_path, chc.to_string())
        .map_err(|err| format!("{rel_path}: failed to write CHC file: {err}"))?;

    let output = solver
        .run(&temp_dir.join(format!("{safe_name}_out")), &chc_path)
        .map_err(|err| format!("{rel_path}: failed to run {}: {err}", solver.name()))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let actual = parse_solver_result(&stdout)
        .or_else(|| parse_solver_result(&stderr))
        .ok_or_else(|| {
            format!(
                "{rel_path}: {} did not print a solver result\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
                solver.name(),
                output.status,
                stdout,
                stderr
            )
        })?;

    if !output.status.success() {
        return Err(format!(
            "{rel_path}: {} exited with {}\nstdout:\n{}\nstderr:\n{}",
            solver.name(),
            output.status,
            stdout,
            stderr
        ));
    }

    if !expected.contains(&actual) {
        let expected = expected
            .iter()
            .map(|result| result.as_str())
            .collect::<Vec<_>>()
            .join(" or ");
        return Err(format!(
            "{rel_path}: expected {expected}, got {}\nstdout:\n{}\nstderr:\n{}",
            actual.as_str(),
            stdout,
            stderr
        ));
    }

    Ok(())
}

fn run_hoice(out_dir: &Path, chc_path: &Path) -> std::io::Result<Output> {
    let timeout = env::var("HOICE_BENCH_TIMEOUT_SECS").unwrap_or_else(|_| "60".to_string());
    Command::new("hoice")
        .args(["-q", "--color", "off", "-t", &timeout, "--out_dir"])
        .arg(out_dir)
        .arg(chc_path)
        .output()
}

fn run_z3(chc_path: &Path) -> std::io::Result<Output> {
    let timeout = env::var("Z3_BENCH_TIMEOUT_SECS").unwrap_or_else(|_| "60".to_string());
    let timeout_arg = format!("-T:{timeout}");
    Command::new("z3")
        .arg("-smt2")
        .arg(timeout_arg)
        .arg(chc_path)
        .output()
}

fn parse_solver_result(output: &str) -> Option<SolverResult> {
    output.lines().rev().find_map(|line| match line.trim() {
        "sat" => Some(SolverResult::Sat),
        "unsat" => Some(SolverResult::Unsat),
        "timeout" => Some(SolverResult::Timeout),
        _ => None,
    })
}

fn sanitize_path(path: &str) -> String {
    path.chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect()
}
