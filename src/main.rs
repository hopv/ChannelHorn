use anyhow::Result;
use channel_rust_impl::chc;
use channel_rust_impl::core::{eval, parser};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(version)]
struct Args {
    #[arg(short, long)]
    file: String,

    #[arg(long, default_value_t = false)]
    no_timestamps: bool,

    #[arg(short, long)]
    exec: bool,

    #[arg(short, long)]
    output: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let filename = args.file;

    let input_content = std::fs::read_to_string(&filename)?;
    let ast = parser::parse_program(&input_content)?;

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
    })?;

    if let Some(output_filename) = args.output {
        std::fs::write(output_filename, output_chc.to_string())?;
    } else {
        println!("{}", output_chc);
    }

    Ok(())
}
