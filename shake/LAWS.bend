# shake: the laws. The human states them; PROOF.bend must prove them.
import Base
import ./main.bend as Shake
import ./sample.bend as Sample
import ./args.bend as Args

# the fixture parse, as one line
def shown.of(av: List<&2, String>) -> String:
  Shake.show(Shake.parse(Sample.spec(), av))

# the fixture's root help page
def gold.root() -> String:
  "demo 0.1.0\n" ++
  "A tiny command-line program.\n\n" ++
  "Usage: demo [OPTIONS] [COMMAND]\n\n" ++
  "Commands:\n" ++
  "  greet  Print a greeting\n" ++
  "  add    Add two numbers\n" ++
  "  help   Print this message or the help of the given subcommand(s)\n\n" ++
  "Options:\n" ++
  "  -v, --verbose  More output\n\n"

# the fixture's greet help page
def gold.greet() -> String:
  "greet\n" ++
  "Print a greeting\n\n" ++
  "Usage: demo greet [OPTIONS] [WHO]\n\n" ++
  "Commands:\n" ++
  "  help  Print this message or the help of the given subcommand(s)\n\n" ++
  "Options:\n" ++
  "  -n, --name <NAME>  Who to greet [default: world]\n" ++
  "  -v, --verbose      More output\n\n"

# the fixture's add help page
def gold.add() -> String:
  "add\n" ++
  "Add two numbers\n\n" ++
  "Usage: demo add [OPTIONS] <A> <B> [COMMAND]\n\n" ++
  "Commands:\n" ++
  "  more  A nested add\n" ++
  "  help  Print this message or the help of the given subcommand(s)\n\n" ++
  "Options:\n" ++
  "    --color <COLOR>  A color [possible values: red, green, blue]\n\n"

# the rest fixture parse, as one line
def shown.rest(av: List<&2, String>) -> String:
  Shake.show(Shake.parse(Sample.rest_spec(), av))

# the required-rest fixture parse, as one line
def shown.rest_req(av: List<&2, String>) -> String:
  Shake.show(Shake.parse(Sample.rest_req(), av))

# the rest fixture's files, or empty on error
def files.of(r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) ->
  List<&2, String>:
  match r:
    case Done{m}:
      Shake.get_all(m, "files")
    case Fail{_e}:
      []

# the rest fixture's help page
def gold.rest() -> String:
  "lint\n" ++
  "Lint files.\n\n" ++
  "Usage: lint [FILES]...\n\n" ++
  "Commands:\n" ++
  "  help  Print this message or the help of the given subcommand(s)\n\n"

# the fixture's unexpected-flag error
def gold.err_nope() -> String:
  "error: unexpected argument '--nope' found\n\n" ++
  "Usage: demo [OPTIONS] [COMMAND]\n\n" ++
  "For more information, try 'help'.\n"

# LAW: `app` is the Cli of its fields
law app_is_cli:
  for +name: String
  for +about: String
  for version: Maybe<&2, String>
  for args: List<&2, Shake.Arg>
  for subs: List<&2, Shake.Sub>
  {Shake.app(name, about, version, args, subs)
    == Shake.Cli{name, about, version, args, subs} : Shake.Cli}

# LAW: `sub` is the Sub of its fields
law sub_is_sub:
  for +name: String
  for +about: String
  for args: List<&2, Shake.Arg>
  for subs: List<&2, Shake.Sub>
  {Shake.sub(name, about, args, subs)
    == Shake.Sub{name, about, args, subs} : Shake.Sub}

# LAW: a flag is an unbound Arg with no default and no choices
law flag_is_arg:
  for +name: String
  for short: Maybe<&2, String>
  for long: Maybe<&2, String>
  for +help: String
  {Shake.flag(name, short, long, help)
    == Shake.Arg{name, short, long, Shake.Flag{}, help, False{}, None{}, []}
    : Shake.Arg}

# LAW: an option is an Arg that carries required, default and choices
law opt_is_arg:
  for +name: String
  for short: Maybe<&2, String>
  for long: Maybe<&2, String>
  for +help: String
  for required: Bool
  for default: Maybe<&2, String>
  for choices: List<&2, String>
  {Shake.opt(name, short, long, help, required, default, choices)
    == Shake.Arg{name, short, long, Shake.Opt{}, help, required, default, choices}
    : Shake.Arg}

# LAW: a positional has no short or long spelling
law pos_is_arg:
  for +name: String
  for +help: String
  for required: Bool
  for default: Maybe<&2, String>
  for choices: List<&2, String>
  {Shake.pos(name, help, required, default, choices)
    == Shake.Arg{name, None{}, None{}, Shake.Pos{}, help, required, default, choices}
    : Shake.Arg}

# LAW: a rest positional has no short or long spelling
law rest_is_arg:
  for +name: String
  for +help: String
  for required: Bool
  for default: Maybe<&2, String>
  for choices: List<&2, String>
  {Shake.rest(name, help, required, default, choices)
    == Shake.Arg{name, None{}, None{}, Shake.Rest{}, help, required, default, choices}
    : Shake.Arg}

# LAW: a flag token starts with `-` and is not `-` alone
law looks_flag_is_dash:
  for s: String
  {Shake.looks_flag(s)
    == Bool.and(String.starts_with(s, "-"), Bool.not(String.eq(s, "-"))) : Bool}

# LAW: a token that starts `--` is a flag
law looks_flag_long:
  for s: String
  {Shake.looks_flag("--" ++ s) == True{} : Bool}

# LAW: `-` alone is not a flag
law looks_flag_alone:
  for u: Unit
  {Shake.looks_flag("-") == False{} : Bool}

# LAW: `cut_eq` is the walk of the string's chars
law cut_eq_is_go:
  for s: String
  {Shake.cut_eq(s) == Shake.cut_eq.go(String.to_list(s), [])
    : String & Maybe<&2, String>}

# LAW: a token with no `=` is the name and no value
law cut_eq_plain:
  for u: Unit
  {Shake.cut_eq("name") == ("name", None{}) : String & Maybe<&2, String>}

# LAW: `name=value` splits at the first `=`
law cut_eq_value:
  for u: Unit
  {Shake.cut_eq("name=Ada") == ("name", Some{"Ada"})
    : String & Maybe<&2, String>}

# LAW: `short_of` is take 1 and drop 1
law short_of_is_take:
  for s: String
  {Shake.short_of(s) == Shake.short_of.go(String.take(s, 1n), String.drop(s, 1n))
    : String & Maybe<&2, String>}

# LAW: a glued short option is the first char and the rest
law short_of_glued:
  for u: Unit
  {Shake.short_of("nAda") == ("n", Some{"Ada"}) : String & Maybe<&2, String>}

# LAW: a one-char short has no glued value
law short_of_one:
  for u: Unit
  {Shake.short_of("n") == ("n", None{}) : String & Maybe<&2, String>}

# LAW: no Arg has a long spelling in an empty list
law by_long_nil:
  for name: String
  {Shake.by_long([], name) == None{} : Maybe<&2, Shake.Arg>}

# LAW: the verbose flag is found by its long spelling
law by_long_flag:
  for u: Unit
  {Shake.by_long([Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
      "verbose")
    == Some{Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")}
    : Maybe<&2, Shake.Arg>}

# LAW: no Arg has a short spelling in an empty list
law by_short_nil:
  for name: String
  {Shake.by_short([], name) == None{} : Maybe<&2, Shake.Arg>}

# LAW: the verbose flag is found by its short spelling
law by_short_flag:
  for u: Unit
  {Shake.by_short([Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
      "v")
    == Some{Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")}
    : Maybe<&2, Shake.Arg>}

# LAW: no Arg has a binding name in an empty list
law by_name_nil:
  for name: String
  {Shake.by_name([], name) == None{} : Maybe<&2, Shake.Arg>}

# LAW: an Arg is found by its binding name
law by_name_flag:
  for u: Unit
  {Shake.by_name([Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")],
      "verbose")
    == Some{Shake.flag("verbose", Some{"v"}, Some{"verbose"}, "More output")}
    : Maybe<&2, Shake.Arg>}

# LAW: no Sub is found in an empty list
law find_sub_nil:
  for name: String
  {Shake.find_sub([], name) == None{} : Maybe<&2, Shake.Sub>}

# LAW: a Sub is found by its name
law find_sub_head:
  for u: Unit
  {Shake.find_sub([Shake.sub("greet", "Print a greeting", [], [])], "greet")
    == Some{Shake.sub("greet", "Print a greeting", [], [])}
    : Maybe<&2, Shake.Sub>}

# LAW: an empty spec has no positionals
law pos_of_nil:
  for u: Unit
  {Shake.pos_of([]) == [] : List<&2, Shake.Arg>}

# LAW: `pos_of` keeps positionals and drops flags
law pos_of_keeps:
  for u: Unit
  {Shake.pos_of([Shake.flag("verbose", None{}, Some{"verbose"}, "More output"),
      Shake.pos("who", "Who to greet", False{}, None{}, [])])
    == [Shake.pos("who", "Who to greet", False{}, None{}, [])]
    : List<&2, Shake.Arg>}

# LAW: `pos_of` keeps a rest positional
law pos_of_rest:
  for u: Unit
  {Shake.pos_of([Shake.rest("files", "Files to lint", False{}, None{}, [])])
    == [Shake.rest("files", "Files to lint", False{}, None{}, [])]
    : List<&2, Shake.Arg>}

# LAW: no rest is last
law rest_last_none:
  for u: Unit
  {Shake.rest.last([Shake.pos("who", "Who to greet", False{}, None{}, [])])
    == True{} : Bool}

# LAW: rest is last when it ends the positionals
law rest_last_ok:
  for u: Unit
  {Shake.rest.last([Shake.pos("who", "Who to greet", False{}, None{}, []),
      Shake.rest("files", "Files to lint", False{}, None{}, [])])
    == True{} : Bool}

# LAW: rest is not last when a positional follows it
law rest_last_mid:
  for u: Unit
  {Shake.rest.last([Shake.rest("files", "Files to lint", False{}, None{}, []),
      Shake.pos("who", "Who to greet", False{}, None{}, [])])
    == False{} : Bool}

# LAW: empty choices accept any value
law allowed_any:
  for v: String
  {Shake.allowed([], v) == True{} : Bool}

# LAW: a listed value is allowed
law allowed_listed:
  for u: Unit
  {Shake.allowed(["red", "green"], "red") == True{} : Bool}

# LAW: a value not listed is refused
law allowed_other:
  for u: Unit
  {Shake.allowed(["red", "green"], "blue") == False{} : Bool}

# LAW: nothing is bound in an empty list
law bound_nil:
  for name: String
  {Shake.bound([], name) == False{} : Bool}

# LAW: a bind's own name is bound
law bound_head:
  for u: Unit
  {Shake.bound([Shake.Bind{"name", "Ada"}], "name") == True{} : Bool}

# LAW: an empty match binds every name to ""
law get_nil:
  for name: String
  {Shake.get(Shake.Matched{[], []}, name) == "" : String}

# LAW: `get` reads the bound value
law get_head:
  for u: Unit
  {Shake.get(Shake.Matched{[], [Shake.Bind{"name", "Ada"}]}, "name")
    == "Ada" : String}

# LAW: `get_all` on an empty match is empty
law get_all_nil:
  for name: String
  {Shake.get_all(Shake.Matched{[], []}, name) == [] : List<&2, String>}

# LAW: `get_all` keeps every bound value of that name
law get_all_two:
  for u: Unit
  {Shake.get_all(Shake.Matched{[],
      [Shake.Bind{"files", "a.bend"}, Shake.Bind{"files", "b.bend"}]}, "files")
    == ["a.bend", "b.bend"] : List<&2, String>}

# LAW: an empty match has no flag set
law on_nil:
  for name: String
  {Shake.on(Shake.Matched{[], []}, name) == False{} : Bool}

# LAW: a flag bound to "true" is on
law on_true:
  for u: Unit
  {Shake.on(Shake.Matched{[], [Shake.Bind{"verbose", "true"}]}, "verbose")
    == True{} : Bool}

# LAW: `path_of` is the match's command path
law path_of_keeps:
  for path: List<&2, String>
  for binds: List<&2, Shake.Bind>
  {Shake.path_of(Shake.Matched{path, binds}) == path : List<&2, String>}

# LAW: `parse` is the finished walk of argv
law parse_is_walk:
  for app: Shake.Cli
  for argv: List<&2, String>
  {Shake.parse(app, argv)
    == Shake.parse.finish(Shake.parse.walk(argv, Shake.parse.start(app)))
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: a successful parse shows as `ok path | binds`
law show_done:
  for m: Shake.Matched
  {Shake.show(Done{m}) == "ok " ++ Shake.show.matched(m) : String}

# LAW: a failed parse shows as `err` and the tag
law show_fail:
  for e: Shake.ParseErr
  {Shake.show(Fail{e}) == "err " ++ Shake.show.err(e) : String}

# LAW: `help` is the page at the end of the path
law help_is_go:
  for +name: String
  for +about: String
  for version: Maybe<&2, String>
  for args: List<&2, Shake.Arg>
  for subs: List<&2, Shake.Sub>
  for path: List<&2, String>
  {Shake.help(Shake.Cli{name, about, version, args, subs}, path)
    == Shake.help.go(path, Shake.How{name, about, version, args, subs, name})
    : String}

# LAW: NeedHelp has no error text; the caller prints `help`
law err_text_help:
  for app: Shake.Cli
  for path: List<&2, String>
  {Shake.err_text(app, Shake.NeedHelp{path}) == "" : String}

# LAW: `--verbose greet` binds the flag and the name default
law parse_flag_long:
  for u: Unit
  {shown.of(["--verbose", "greet"]) == "ok greet | verbose=true name=world"
    : String}

# LAW: `-v greet` is the same as `--verbose greet`
law parse_flag_short:
  for u: Unit
  {shown.of(["-v", "greet"]) == "ok greet | verbose=true name=world" : String}

# LAW: `--name Ada` binds the option
law parse_opt_long:
  for u: Unit
  {shown.of(["greet", "--name", "Ada"]) == "ok greet | name=Ada" : String}

# LAW: `--name=Ada` binds the option
law parse_opt_eq:
  for u: Unit
  {shown.of(["greet", "--name=Ada"]) == "ok greet | name=Ada" : String}

# LAW: `-n Ada` binds the option
law parse_opt_short:
  for u: Unit
  {shown.of(["greet", "-n", "Ada"]) == "ok greet | name=Ada" : String}

# LAW: `-nAda` binds the glued short option
law parse_opt_glued:
  for u: Unit
  {shown.of(["greet", "-nAda"]) == "ok greet | name=Ada" : String}

# LAW: a bare word after `greet` is the `who` positional
law parse_pos:
  for u: Unit
  {shown.of(["greet", "Ada"]) == "ok greet | who=Ada name=world" : String}

# LAW: `greet` alone fills the name default
law parse_default:
  for u: Unit
  {shown.of(["greet"]) == "ok greet | name=world" : String}

# LAW: `add` takes two required positionals
law parse_add:
  for u: Unit
  {shown.of(["add", "2", "3"]) == "ok add | a=2 b=3" : String}

# LAW: `add 2 3 more` selects the nested command
law parse_nested:
  for u: Unit
  {shown.of(["add", "2", "3", "more"]) == "ok add/more | a=2 b=3" : String}

# LAW: `--` passes the next word through as a positional
law parse_dash:
  for u: Unit
  {shown.of(["greet", "--", "--name"]) == "ok greet | who=--name name=world"
    : String}

# LAW: a missing required positional is `missing`
law err_missing:
  for u: Unit
  {shown.of(["add", "2"]) == "err missing b" : String}

# LAW: a value outside the choices is `bad`
law err_choice:
  for u: Unit
  {shown.of(["add", "2", "3", "--color", "purple"]) == "err bad color purple"
    : String}

# LAW: an unknown long flag is `unknown`
law err_unknown_long:
  for u: Unit
  {shown.of(["--nope"]) == "err unknown --nope" : String}

# LAW: an unknown short flag is `unknown`
law err_unknown_short:
  for u: Unit
  {shown.of(["-z"]) == "err unknown -z" : String}

# LAW: `help` is NeedHelp at the root
law err_help_root:
  for u: Unit
  {shown.of(["help"]) == "err help " : String}

# LAW: `help greet` is NeedHelp at greet
law err_help_greet:
  for u: Unit
  {shown.of(["help", "greet"]) == "err help greet" : String}

# LAW: a leftover word after the positionals is `unexpected`
law err_unexpected:
  for u: Unit
  {shown.of(["greet", "Ada", "extra"]) == "err unexpected extra" : String}

# LAW: zero leftovers bind rest to an empty list
law parse_rest_none:
  for u: Unit
  {files.of(Shake.parse(Sample.rest_spec(), [])) == [] : List<&2, String>}

# LAW: one leftover is a rest list of one
law parse_rest_one:
  for u: Unit
  {files.of(Shake.parse(Sample.rest_spec(), ["a.bend"]))
    == ["a.bend"] : List<&2, String>}

# LAW: many leftovers are the rest list
law parse_rest_many:
  for u: Unit
  {files.of(Shake.parse(Sample.rest_spec(), ["a.bend", "b.bend"]))
    == ["a.bend", "b.bend"] : List<&2, String>}

# LAW: `--` passes the next words through as the rest list
law parse_rest_dash:
  for u: Unit
  {files.of(Shake.parse(Sample.rest_spec(), ["--", "--name", "a.bend"]))
    == ["--name", "a.bend"] : List<&2, String>}

# LAW: a required rest with no leftovers is `missing`
law err_rest_missing:
  for u: Unit
  {shown.rest_req([]) == "err missing files" : String}

# LAW: the rest fixture parse shows every leftover
law show_rest_many:
  for u: Unit
  {shown.rest(["a.bend", "b.bend"]) == "ok  | files=a.bend files=b.bend"
    : String}

# LAW: the fixture's root help page is this exact text
law help_root:
  for u: Unit
  {Shake.help(Sample.spec(), []) == gold.root() : String}

# LAW: the fixture's greet help page is this exact text
law help_greet:
  for u: Unit
  {Shake.help(Sample.spec(), ["greet"]) == gold.greet() : String}

# LAW: the fixture's add help page is this exact text
law help_add:
  for u: Unit
  {Shake.help(Sample.spec(), ["add"]) == gold.add() : String}

# LAW: a rest positional shows as `[NAME]...`
law help_rest:
  for u: Unit
  {Shake.help(Sample.rest_spec(), []) == gold.rest() : String}

# LAW: a required rest positional shows as `<NAME>...`
law help_rest_req:
  for u: Unit
  {Shake.help.pos.one(Shake.rest("files", "Files to lint", True{}, None{}, []))
    == " <FILES>..." : String}

# LAW: an unknown flag's error names the flag and the root usage
law err_text_unknown:
  for u: Unit
  {Shake.err_text(Sample.spec(), Shake.UnknownFlag{"--nope"}) == gold.err_nope()
    : String}

# LAW: the empty argv list copies to empty
law copy_nil:
  for u: Unit
  {Args.copy(Nil{}) == Nil{} : List<&2, String>}

# LAW: a one-word argv list copies that word
law copy_one:
  for +h: String
  {Args.copy(h <> Nil{}) == h <> Nil{} : List<&2, String>}

# LAW: `argv` is `IO.args` copied to a reusable list
law argv_is_copy:
  for u: Unit
  {Args.argv()
    == IO.bind(List<&1, String>, List<&2, String>, IO.args(),
      xs => IO.pure(List<&2, String>, Args.copy(xs)))
    : IO(List<&2, String>)}
