mod analyze;

fn main() {
    let mut pargs = pico_args::Arguments::from_env();
    if let Some(cmd) = pargs.subcommand().expect("failed to parse arguments") {
        match cmd.as_ref() {
            "analyze" => {
                analyze::analyze();
            },
            "frequencies" => {
                analyze::frequencies();
            },
            _ => {},
        }
    }
}
