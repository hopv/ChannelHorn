use anyhow::{Result, anyhow};
use channel_horn::chc;
use channel_horn::core::{eval, parser};
use channel_horn::sugar;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version)]
struct Args {
    #[arg(short, long)]
    file: String,

    #[arg(long, default_value_t = false)]
    no_timestamps: bool,

    #[arg(long, default_value_t = false)]
    deadlock: bool,

    #[arg(short, long)]
    exec: bool,

    #[arg(short, long)]
    output: Option<String>,

    #[arg(short, long, default_value_t = false)]
    sugar: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let filename = args.file;

    let input_content = std::fs::read_to_string(&filename)?;
    let ast = if args.sugar {
        let sugar_ast = sugar::parser::parse_program(&input_content)?;
        sugar::check::check_program(&sugar_ast)
            .map_err(|e| anyhow!("sugar check error: {:?}", e))?;
        sugar::desugar::desugar_program(&sugar_ast)?
    } else {
        parser::parse_program(&input_content)?
    };
    if args.sugar {
        println!("{}", ast);
    }

    if args.exec {
        let mut evaluator = eval::Evaluator::new(ast.clone())?;
        loop {
            if let Err(e) = evaluator.step() {
                eprintln!("Execution error: {}", e);
                break;
            }
            if evaluator.is_done() {
                println!("Program completed successfully.");
                break;
            }
        }
    }

    let output_chc = ast.lower_to_chc(chc::Setting {
        no_timestamps: args.no_timestamps,
        check_mode: if args.deadlock {
            chc::CheckMode::DeadlockFreedom
        } else {
            chc::CheckMode::FailReachability
        },
    })?;

    if let Some(output_filename) = args.output {
        std::fs::write(output_filename, output_chc.to_string())?;
    } else {
        println!("{}", output_chc);
    }

    Ok(())
}
