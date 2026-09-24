# shake/cli: the parser behind main.bend, internal. `parse` reads argv
# against a Cli; `help` writes usage for a command path, and `help` is the
# subcommand that asks for it. A `--` that reaches `parse` ends option
# parsing; in a compiled program the runtime takes the first `--` itself.
import Base

# a flag, a valued option, a positional, or a rest positional
type ArgKind is Data:
  Flag{}
  Opt{}
  Pos{}
  Rest{}

# one argument: name is the binding key; short/long are the CLI spellings
type Arg is Data:
  Arg{
    name: String,
    short: Maybe<&2, String>,
    long: Maybe<&2, String>,
    kind: ArgKind,
    help: String,
    required: Bool,
    default: Maybe<&2, String>,
    choices: List<&2, String>
  }

# a nested command
type Sub is Data:
  Sub{
    name: String,
    about: String,
    args: List<&2, Arg>,
    subcommands: List<&2, Sub>
  }

# the program: name, about, optional version, top-level args and commands
type Cli is Data:
  Cli{
    name: String,
    about: String,
    version: Maybe<&2, String>,
    args: List<&2, Arg>,
    subcommands: List<&2, Sub>
  }

# one bound name and its text
type Bind is Data:
  Bind{name: String, value: String}

# a successful parse: selected command path and the bindings
type Matched is Data:
  Matched{+path: List<&2, String>, +binds: List<&2, Bind>}

# a failed parse. NeedHelp is `help` / `help <path>`
type ParseErr is Data:
  UnknownFlag{flag: String}
  Missing{name: String}
  BadValue{name: String, value: String}
  NeedHelp{path: List<&2, String>}
  Unexpected{arg: String}

# how the next token is read
type Mode is Data:
  Free{}
  Need{name: String}
  Help{}
  Dead{err: ParseErr}

# the walker: current spec, accumulated specs, selected path, bindings
type St is Data:
  St{
    mode: Mode,
    args: List<&2, Arg>,
    specs: List<&2, Arg>,
    subs: List<&2, Sub>,
    path: List<&2, String>,
    binds: List<&2, Bind>,
    pos: List<&2, Arg>,
    raw: Bool,
    seen: Bool
  }

# the page a help walk has reached
type How is Data:
  How{
    bin: String,
    about: String,
    version: Maybe<&2, String>,
    args: List<&2, Arg>,
    subs: List<&2, Sub>,
    usage: String
  }

# a program spec
def app(
  +name: String,
  +about: String,
  version: Maybe<&2, String>,
  args: List<&2, Arg>,
  subs: List<&2, Sub>
) -> Cli:
  Cli{name, about, version, args, subs}

# a nested command
def sub(
  +name: String,
  +about: String,
  args: List<&2, Arg>,
  subs: List<&2, Sub>
) -> Sub:
  Sub{name, about, args, subs}

# a boolean flag
def flag(
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String
) -> Arg:
  Arg{name, short, long, Flag{}, help, False{}, None{}, []}

# a valued option
def opt(
  +name: String,
  short: Maybe<&2, String>,
  long: Maybe<&2, String>,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> Arg:
  Arg{name, short, long, Opt{}, help, required, default, choices}

# a positional
def pos(
  +name: String,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> Arg:
  Arg{name, None{}, None{}, Pos{}, help, required, default, choices}

# a rest positional: every leftover word, as one name
def rest(
  +name: String,
  +help: String,
  required: Bool,
  default: Maybe<&2, String>,
  choices: List<&2, String>
) -> Arg:
  Arg{name, None{}, None{}, Rest{}, help, required, default, choices}

# the larger of two Nats
def help.max(+aa: Nat, +bb: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(aa, bb), bb, aa)

# n spaces
def help.spaces(nn: Nat) -> String:
  match nn:
    case 0n:
      ""
    case 1n+p:
      " " ++ help.spaces(p)

# s padded on the right to width n
def help.pad(+ss: String, nn: Nat) -> String:
  ss ++ help.spaces(Nat.sub(nn, String.length(ss)))

# a Maybe string's text, or the default
def text.of(mm: Maybe<&2, String>, +dd: String) -> String:
  Maybe.default(&2, String, mm, dd)

# whether a string is a flag token (`-` alone is not)
def looks_flag(+ss: String) -> Bool:
  Bool.and(String.starts_with(ss, "-"), Bool.not(String.eq(ss, "-")))

# chars reversed into a string
def from.rev(cs: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, cs))

# `name` and an optional `=value`, once the next char is known
def cut_eq.pick(
  eq: Bool,
  acc: List<&2, Char>,
  tt: List<&2, Char>,
  rest: String & Maybe<&2, String>
) -> String & Maybe<&2, String>:
  match eq:
    case True{}:
      (from.rev(acc), Some{String.from_list(tt)})
    case False{}:
      rest

# one char of a `name=value` cut
def cut_eq.chr(
  +cc: Char,
  tt: List<&2, Char>,
  acc: List<&2, Char>,
  rest: String & Maybe<&2, String>
) -> String & Maybe<&2, String>:
  cut_eq.pick(Char.is_eq(cc, '='), acc, tt, rest)

# `name` and an optional `=value` from the body after `--`
def cut_eq.go(
  cs: List<&2, Char>,
  +acc: List<&2, Char>
) -> String & Maybe<&2, String>:
  match cs:
    case Nil{}:
      (from.rev(acc), None{})
    case Con{+c, +t}:
      cut_eq.chr(c, t, acc, cut_eq.go(t, c <> acc))

# `name` and an optional `=value`
def cut_eq(ss: String) -> String & Maybe<&2, String>:
  cut_eq.go(String.to_list(ss), [])

# a short spelling and a glued value
def short_of.go(+name: String, +rest: String) -> String & Maybe<&2, String>:
  (name, Bool.pick(Maybe<&2, String>, String.is_empty(rest), None{}, Some{rest}))

# the short name and optional glued value of the body after `-`
def short_of(+ss: String) -> String & Maybe<&2, String>:
  short_of.go(String.take(ss, 1n), String.drop(ss, 1n))

# whether this Arg's long spelling is `name`
def by_long.hit(aa: Arg, +name: String) -> Bool:
  Arg{_n, _s, long, _k, _h, _r, _d, _c} = aa
  String.eq(text.of(long, ""), name)

# this Arg when the long spelling matches, else the rest
def by_long.at(hit: Bool, hh: Arg, rest: Maybe<&2, Arg>) -> Maybe<&2, Arg>:
  match hit:
    case True{}:
      Some{hh}
    case False{}:
      rest

# the Arg with this long spelling, if any
def by_long(args: List<&2, Arg>, +name: String) -> Maybe<&2, Arg>:
  match args:
    case Nil{}:
      None{}
    case Con{+h, t}:
      by_long.at(by_long.hit(h, name), h, by_long(t, name))

# whether this Arg's short spelling is `name`
def by_short.hit(aa: Arg, +name: String) -> Bool:
  Arg{_n, short, _l, _k, _h, _r, _d, _c} = aa
  String.eq(text.of(short, ""), name)

# this Arg when the short spelling matches, else the rest
def by_short.at(hit: Bool, hh: Arg, rest: Maybe<&2, Arg>) -> Maybe<&2, Arg>:
  match hit:
    case True{}:
      Some{hh}
    case False{}:
      rest

# the Arg with this short spelling, if any
def by_short(args: List<&2, Arg>, +name: String) -> Maybe<&2, Arg>:
  match args:
    case Nil{}:
      None{}
    case Con{+h, t}:
      by_short.at(by_short.hit(h, name), h, by_short(t, name))

# whether this Arg's name is `name`
def by_name.hit(aa: Arg, +name: String) -> Bool:
  Arg{+n, _s, _l, _k, _h, _r, _d, _c} = aa
  String.eq(n, name)

# this Arg when the binding name matches, else the rest
def by_name.at(hit: Bool, hh: Arg, rest: Maybe<&2, Arg>) -> Maybe<&2, Arg>:
  match hit:
    case True{}:
      Some{hh}
    case False{}:
      rest

# the Arg with this binding name, if any
def by_name(args: List<&2, Arg>, +name: String) -> Maybe<&2, Arg>:
  match args:
    case Nil{}:
      None{}
    case Con{+h, t}:
      by_name.at(by_name.hit(h, name), h, by_name(t, name))

# this Sub when its name matches, else the rest
def find_sub.at(ss: Sub, rest: Maybe<&2, Sub>, +name: String) -> Maybe<&2, Sub>:
  Sub{+n, _a, _g, _c} = ss
  Bool.pick(Maybe<&2, Sub>, String.eq(n, name), Some{ss}, rest)

# the Sub with this name, if any
def find_sub(subs: List<&2, Sub>, +name: String) -> Maybe<&2, Sub>:
  match subs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      find_sub.at(h, find_sub(t, name), name)

# whether this Arg is a positional
def pos.is.kind(kk: ArgKind) -> Bool:
  match kk:
    case Pos{}:
      True{}
    case Rest{}:
      True{}
    case Flag{}:
      False{}
    case Opt{}:
      False{}

# whether this ArgKind is rest
def rest.is.kind(kk: ArgKind) -> Bool:
  match kk:
    case Rest{}:
      True{}
    case Pos{}:
      False{}
    case Flag{}:
      False{}
    case Opt{}:
      False{}

# whether this Arg is a positional
def pos.is(aa: Arg) -> Bool:
  Arg{_n, _s, _l, kind, _h, _r, _d, _c} = aa
  pos.is.kind(kind)

# whether this Arg is a rest positional
def rest.is(aa: Arg) -> Bool:
  Arg{_n, _s, _l, kind, _h, _r, _d, _c} = aa
  rest.is.kind(kind)

# this Arg kept when it is a positional
def pos_of.put(keep: Bool, hh: Arg, rest: List<&2, Arg>) -> List<&2, Arg>:
  match keep:
    case True{}:
      hh <> rest
    case False{}:
      rest

# the positionals of a spec, in order
def pos_of(args: List<&2, Arg>) -> List<&2, Arg>:
  match args:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      pos_of.put(pos.is(h), h, pos_of(t))

# a rest is last only when nothing follows
def rest.last.hit(is_rest: Bool, empty: Bool, tail_ok: Bool) -> Bool:
  match is_rest:
    case True{}:
      empty
    case False{}:
      tail_ok

# whether rest positionals are last (and at most one)
def rest.last(pos: List<&2, Arg>) -> Bool:
  match pos:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      rest.last.hit(rest.is(h), List.is_empty(&2, Arg, t), rest.last(t))

# whether `v` is among the choices; an empty list accepts any value
def allowed.ok.at(hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest

# whether `v` is listed; the empty list answers no
def allowed.ok(cs: List<&2, String>, +vv: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      allowed.ok.at(String.eq(h, vv), allowed.ok(t, vv))

# empty choices accept any value; otherwise `v` must be listed
def allowed(+cs: List<&2, String>, +vv: String) -> Bool:
  Bool.or(List.is_empty(&2, String, cs), allowed.ok(cs, vv))

# whether this bind's name is `name`
def bound.hit(bb: Bind, +name: String) -> Bool:
  Bind{+n, _v} = bb
  String.eq(n, name)

# True when the head matches, else the rest
def bound.at(hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest

# whether `name` is already bound
def bound(bs: List<&2, Bind>, +name: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      bound.at(bound.hit(h, name), bound(t, name))

# this bind's value when the name matches, else the rest
def get_all.bind.hit(
  hit: Bool,
  +vv: String,
  more: List<&2, String>
) -> List<&2, String>:
  match hit:
    case True{}:
      vv <> more
    case False{}:
      more

# this bind's value when the name matches, else the rest
def get_all.bind.at(
  bb: Bind,
  more: List<&2, String>,
  +name: String
) -> List<&2, String>:
  Bind{+n, v} = bb
  get_all.bind.hit(String.eq(n, name), v, more)

# every value bound to `name`
def get_all.bind(bs: List<&2, Bind>, +name: String) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{+h, t}:
      get_all.bind.at(h, get_all.bind(t, name), name)

# every value bound to `name`
def get_all(mm: Matched, +name: String) -> List<&2, String>:
  Matched{_p, binds} = mm
  get_all.bind(binds, name)

# the last of a list of values, or `dflt` when it is empty
def get.last(vs: List<&2, String>, dflt: String) -> String:
  match vs:
    case Nil{}:
      dflt
    case Con{hh, tt}:
      get.last(tt, hh)

# the value bound to `name` last, or "" when there is none
def get(mm: Matched, +name: String) -> String:
  get.last(get_all(mm, name), "")

# whether a flag named `name` was set
def on(mm: Matched, +name: String) -> Bool:
  String.eq(get(mm, name), "true")

# the selected command path
def path_of(mm: Matched) -> List<&2, String>:
  Matched{path, _b} = mm
  path

# the starting walker for a Cli
def parse.start(app: Cli) -> St:
  Cli{_n, _a, _v, +args, subs} = app
  St{Free{}, args, args, subs, [], [], pos_of(args), False{}, False{}}

# a failed walker that keeps the rest of the state
def parse.dead(
  ee: ParseErr,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  St{Dead{ee}, args, specs, subs, path, binds, pos, raw, seen}

# a successful bind of `name` to `val`
def parse.put(
  +name: String,
  +val: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  St{Free{}, args, specs, subs, path, Bind{name, val} <> binds, pos, raw, seen}

# the choices of a found Arg, or none
def parse.choices(mm: Maybe<&2, Arg>) -> List<&2, String>:
  match mm:
    case None{}:
      []
    case Some{a}:
      Arg{_n, _s, _l, _k, _h, _r, _d, cs} = a
      cs

# bind `name` to `val` when the value is allowed
def parse.take_choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match ok:
    case True{}:
      parse.put(name, val, args, specs, subs, path, binds, pos, raw, seen)
    case False{}:
      parse.dead(BadValue{name, val}, args, specs, subs, path, binds, pos, raw, seen)

# bind an option that already has its value
def parse.take_opt_val(
  +name: String,
  +val: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  parse.take_choice(allowed(parse.choices(by_name(specs, name)), val), name, val,
    args, specs, subs, path, binds, pos, raw, seen)

# a flag with no glued value is set; a glued value is unexpected
def parse.take_flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match val:
    case None{}:
      parse.put(name, "true", args, specs, subs, path, binds, pos, raw, seen)
    case Some{_v}:
      parse.dead(Unexpected{orig}, args, specs, subs, path, binds, pos, raw, seen)

# an option: glued value now, or the next token
def parse.take_opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match val:
    case None{}:
      St{Need{name}, args, specs, subs, path, binds, pos, raw, seen}
    case Some{v}:
      parse.take_opt_val(name, v, args, specs, subs, path, binds, pos, raw, seen)

# dispatch on the found Arg's kind
def parse.take_arg.kind(
  kk: ArgKind,
  +name: String,
  val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match kk:
    case Flag{}:
      parse.take_flag(val, name, orig, args, specs, subs, path, binds, pos, raw, seen)
    case Opt{}:
      parse.take_opt(val, name, args, specs, subs, path, binds, pos, raw, seen)
    case Pos{}:
      parse.dead(UnknownFlag{orig}, args, specs, subs, path, binds, pos, raw, seen)
    case Rest{}:
      parse.dead(UnknownFlag{orig}, args, specs, subs, path, binds, pos, raw, seen)

# a found Arg, or an unknown flag
def parse.take_arg(
  found: Maybe<&2, Arg>,
  val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match found:
    case None{}:
      parse.dead(UnknownFlag{orig}, args, specs, subs, path, binds, pos, raw, seen)
    case Some{a}:
      Arg{+name, _s, _l, kind, _h, _r, _d, _c} = a
      parse.take_arg.kind(kind, name, val, orig, args, specs, subs, path, binds, pos,
        raw, seen)

# a long option with a name, or `--=...`
def parse.take_long.named(
  empty: Bool,
  +name: String,
  val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match empty:
    case True{}:
      parse.dead(UnknownFlag{orig}, args, specs, subs, path, binds, pos, raw, seen)
    case False{}:
      parse.take_arg(by_long(args, name), val, orig, args, specs, subs, path, binds,
        pos, raw, seen)

# a long option after the `=` cut
def parse.take_long.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  (+name, val) = nv
  parse.take_long.named(String.is_empty(name), name, val, orig, args, specs, subs,
    path, binds, pos, raw, seen)

# a long option body after `--`
def parse.take_long(
  body: String,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  parse.take_long.cut(cut_eq(body), orig, args, specs, subs, path, binds, pos, raw,
    seen)

# a short option after the glued-value cut
def parse.take_short.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  (name, val) = nv
  parse.take_arg(by_short(args, name), val, orig, args, specs, subs, path, binds, pos,
    raw, seen)

# a short option body after `-`
def parse.take_short(
  body: String,
  +orig: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  parse.take_short.cut(short_of(body), orig, args, specs, subs, path, binds, pos, raw,
    seen)

# a rest positional stays; a plain one is consumed
def parse.take_pos.keep(keep: Bool, hh: Arg, tt: List<&2, Arg>) -> List<&2, Arg>:
  match keep:
    case True{}:
      hh <> tt
    case False{}:
      tt

# the next remaining positional, or an unexpected word
def parse.take_pos(
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  pos: List<&2, Arg>,
  raw: Bool
) -> St:
  match pos:
    case Nil{}:
      parse.dead(Unexpected{tok}, args, specs, subs, path, binds, pos, raw, True{})
    case Con{+h, t}:
      Arg{+name, _s, _l, _k, _h, _r, _d, +cs} = h
      parse.take_choice(allowed(cs, tok), name, tok, args, specs, subs, path, binds,
        parse.take_pos.keep(rest.is(h), h, t), raw, True{})

# this Sub's spec becomes current; parent bindings stay
def parse.enter(
  ss: Sub,
  +specs: List<&2, Arg>,
  +path: List<&2, String>,
  binds: List<&2, Bind>
) -> St:
  Sub{+name, _a, +next, next_subs} = ss
  St{Free{}, next, List.append(&2, Arg, specs, next), next_subs,
    List.append(&2, String, path, [name]), binds, pos_of(next), False{},
    False{}}

# required and no default → Some{name}
def parse.req.go(req: Bool, bare: Bool, +nn: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, Bool.and(req, bare), Some{nn}, None{})

# a required Arg without a default, as a missing name
def parse.req(aa: Arg) -> Maybe<&2, String>:
  Arg{+n, _s, _l, _k, _h, +req, default, _c} = aa
  parse.req.go(req, Maybe.is_none(&2, String, default), n)

# this missing name, else the rest
def parse.first_req.at(
  here: Maybe<&2, String>,
  rest: Maybe<&2, String>
) -> Maybe<&2, String>:
  match here:
    case Some{n}:
      Some{n}
    case None{}:
      rest

# a rest stays in the list, so it does not block a subcommand
def parse.first_req.skip(skip: Bool, aa: Arg) -> Maybe<&2, String>:
  match skip:
    case True{}:
      None{}
    case False{}:
      parse.req(aa)

# the first leftover required positional
def parse.first_req(pos: List<&2, Arg>) -> Maybe<&2, String>:
  match pos:
    case Nil{}:
      None{}
    case Con{+h, t}:
      parse.first_req.at(parse.first_req.skip(rest.is(h), h), parse.first_req(t))

# a leftover required positional blocks entering a subcommand
def parse.enter_or(
  miss: Maybe<&2, String>,
  ss: Sub,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match miss:
    case None{}:
      parse.enter(ss, specs, path, binds)
    case Some{n}:
      parse.dead(Missing{n}, args, specs, subs, path, binds, pos, raw, seen)

# a found subcommand, or a positional
def parse.word.go(
  found: Maybe<&2, Sub>,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match found:
    case None{}:
      parse.take_pos(tok, args, specs, subs, path, binds, pos, raw)
    case Some{s}:
      parse.enter_or(parse.first_req(pos), s, args, specs, subs, path, binds, pos, raw,
        seen)

# a word: a subcommand, or a positional
def parse.word(
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  parse.word.go(find_sub(subs, tok), tok, args, specs, subs, path, binds, pos,
    raw, seen)

# `-` as a word, or a short option
def parse.step.short.go(
  alone: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match alone:
    case True{}:
      parse.word(tok, args, specs, subs, path, binds, pos, False{}, seen)
    case False{}:
      parse.take_short(String.drop(tok, 1n), tok, args, specs, subs, path, binds, pos,
        False{}, seen)

# `-` alone is a positional; otherwise a short option
def parse.step.short(
  dash: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match dash:
    case True{}:
      parse.step.short.go(String.eq(tok, "-"), tok, args, specs, subs, path, binds,
        pos, seen)
    case False{}:
      parse.word(tok, args, specs, subs, path, binds, pos, False{}, seen)

# `--long` first, then `-s`, then a word
def parse.step.kind.go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match long:
    case True{}:
      parse.take_long(String.drop(tok, 2n), tok, args, specs, subs, path, binds, pos,
        False{}, seen)
    case False{}:
      parse.step.short(dash, tok, args, specs, subs, path, binds, pos, seen)

# a long option, a short option, or a word
def parse.step.kind(
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  parse.step.kind.go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok,
    args, specs, subs, path, binds, pos, seen)

# `help` in command position collects the rest of argv as a path
def parse.step.help(
  hit: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match hit:
    case True{}:
      St{Help{}, args, specs, subs, path, binds, pos, False{}, seen}
    case False{}:
      parse.step.kind(tok, args, specs, subs, path, binds, pos, seen)

# `--` ends option parsing
def parse.step.end(
  end: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match end:
    case True{}:
      St{Free{}, args, specs, subs, path, binds, pos, True{}, seen}
    case False{}:
      parse.step.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args,
        specs, subs, path, binds, pos, seen)

# after `--`, every token is a positional
def parse.step.raw(
  raw: Bool,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +seen: Bool
) -> St:
  match raw:
    case True{}:
      parse.take_pos(tok, args, specs, subs, path, binds, pos, True{})
    case False{}:
      parse.step.end(String.eq(tok, "--"), tok, args, specs, subs, path, binds, pos,
        seen)

# a pending option value: a flag-shaped token is a missing value
def parse.step.need(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match flag:
    case True{}:
      parse.dead(Missing{name}, args, specs, subs, path, binds, pos, raw, seen)
    case False{}:
      parse.take_opt_val(name, tok, args, specs, subs, path, binds, pos, raw, seen)

# one token against the walker
def parse.step.mode(
  mode: Mode,
  +tok: String,
  +args: List<&2, Arg>,
  +specs: List<&2, Arg>,
  +subs: List<&2, Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Bind>,
  +pos: List<&2, Arg>,
  +raw: Bool,
  +seen: Bool
) -> St:
  match mode:
    case Dead{e}:
      St{Dead{e}, args, specs, subs, path, binds, pos, raw, seen}
    case Need{name}:
      parse.step.need(looks_flag(tok), name, tok, args, specs, subs, path, binds, pos,
        raw, seen)
    case Help{}:
      St{Help{}, args, specs, subs, List.append(&2, String, path, [tok]), binds,
        pos, raw, seen}
    case Free{}:
      parse.step.raw(raw, tok, args, specs, subs, path, binds, pos, seen)

# one token
def parse.step(+tok: String, st: St) -> St:
  St{mode, args, specs, subs, path, binds, pending, raw, seen} = st
  parse.step.mode(mode, tok, args, specs, subs, path, binds, pending, raw, seen)

# every token, in order
def parse.walk(argv: List<&2, String>, st: St) -> St:
  match argv:
    case Nil{}:
      st
    case Con{+h, t}:
      parse.walk(t, parse.step(h, st))

# a default value kept when the name is not already bound
def fill.one(
  skip: Bool,
  +name: String,
  +val: String,
  rest: List<&2, Bind>
) -> List<&2, Bind>:
  match skip:
    case True{}:
      rest
    case False{}:
      Bind{name, val} <> rest

# a Some default is filled when unbound
def fill.arg.go(
  dd: Maybe<&2, String>,
  +name: String,
  +binds: List<&2, Bind>
) -> List<&2, Bind>:
  match dd:
    case None{}:
      binds
    case Some{v}:
      fill.one(bound(binds, name), name, v, binds)

# this Arg's default, when it has one and is not bound
def fill.arg(aa: Arg, +binds: List<&2, Bind>) -> List<&2, Bind>:
  Arg{+n, _s, _l, _k, _h, _r, default, _c} = aa
  fill.arg.go(default, n, binds)

# defaults of every spec Arg
def fill.args(args: List<&2, Arg>, +binds: List<&2, Bind>) -> List<&2, Bind>:
  match args:
    case Nil{}:
      binds
    case Con{+h, t}:
      fill.arg(h, fill.args(t, binds))

# a required name that is not bound
def miss.one(
  need: Bool,
  +name: String,
  rest: Maybe<&2, String>
) -> Maybe<&2, String>:
  match need:
    case True{}:
      Some{name}
    case False{}:
      rest

# whether this Arg is required and unbound
def miss.arg(
  aa: Arg,
  +binds: List<&2, Bind>,
  rest: Maybe<&2, String>
) -> Maybe<&2, String>:
  Arg{+n, _s, _l, _k, _h, +req, _d, _c} = aa
  miss.one(Bool.and(req, Bool.not(bound(binds, n))), n, rest)

# the first required name that is not bound
def miss.args(args: List<&2, Arg>, +binds: List<&2, Bind>) -> Maybe<&2, String>:
  match args:
    case Nil{}:
      None{}
    case Con{+h, t}:
      miss.arg(h, binds, miss.args(t, binds))

# a missing required name, or the matched result
def parse.finish.miss(
  mm: Maybe<&2, String>,
  path: List<&2, String>,
  binds: List<&2, Bind>
) -> Result<&2, &2, ParseErr, Matched>:
  match mm:
    case Some{n}:
      Fail{Missing{n}}
    case None{}:
      Done{Matched{path, List.reverse(&2, Bind, binds)}}

# required names after defaults
def parse.finish.ok(
  specs: List<&2, Arg>,
  path: List<&2, String>,
  +binds: List<&2, Bind>
) -> Result<&2, &2, ParseErr, Matched>:
  parse.finish.miss(miss.args(specs, binds), path, binds)

# a finished walker: help, a pending value, an error, or defaults + required
def parse.finish.mode(
  mode: Mode,
  +specs: List<&2, Arg>,
  path: List<&2, String>,
  +binds: List<&2, Bind>
) -> Result<&2, &2, ParseErr, Matched>:
  match mode:
    case Dead{e}:
      Fail{e}
    case Need{name}:
      Fail{Missing{name}}
    case Help{}:
      Fail{NeedHelp{path}}
    case Free{}:
      parse.finish.ok(specs, path, fill.args(specs, binds))

# the walker, finished
def parse.finish(st: St) -> Result<&2, &2, ParseErr, Matched>:
  St{mode, _a, specs, _s, path, binds, _p, _r, _n} = st
  parse.finish.mode(mode, specs, path, binds)

# argv against a Cli
def parse(app: Cli, argv: List<&2, String>) -> Result<&2, &2, ParseErr, Matched>:
  parse.finish(parse.walk(argv, parse.start(app)))

# a ParseErr as a short tag
def show.err(ee: ParseErr) -> String:
  match ee:
    case UnknownFlag{word}:
      "unknown " ++ word
    case Missing{name}:
      "missing " ++ name
    case BadValue{name, value}:
      "bad " ++ name ++ " " ++ value
    case NeedHelp{path}:
      "help " ++ String.join(path, " ")
    case Unexpected{arg}:
      "unexpected " ++ arg

# one bind as `name=value`
def show.bind(bb: Bind, +rest: String) -> String:
  Bind{n, v} = bb
  n ++ "=" ++ v ++ Bool.pick(String, String.is_empty(rest), "", " " ++ rest)

# the bindings as `name=value` words
def show.binds(bs: List<&2, Bind>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+h, t}:
      show.bind(h, show.binds(t))

# a Matched as `path | binds`
def show.matched(mm: Matched) -> String:
  Matched{path, binds} = mm
  String.join(path, "/") ++ " | " ++ show.binds(binds)

# a parse result as a single line
def show(rr: Result<&2, &2, ParseErr, Matched>) -> String:
  match rr:
    case Fail{e}:
      "err " ++ show.err(e)
    case Done{m}:
      "ok " ++ show.matched(m)

# the short/long label of an option, plus a metavar for Opt
def help.label.kind(kk: ArgKind, +name: String, +label: String) -> String:
  match kk:
    case Flag{}:
      label
    case Opt{}:
      label ++ " <" ++ String.to_upper(name) ++ ">"
    case Pos{}:
      label
    case Rest{}:
      label

# `-s, --long` or one of them
def help.label.pair(+short: String, +long: String) -> String:
  Bool.pick(String, String.is_empty(short),
    Bool.pick(String, String.is_empty(long), "", "    --" ++ long),
    Bool.pick(String, String.is_empty(long), "  -" ++ short,
      "  -" ++ short ++ ", --" ++ long))

# the usage label of an option
def help.label(aa: Arg) -> String:
  Arg{+name, short, long, kind, _h, _r, _d, _c} = aa
  help.label.kind(kind, name, help.label.pair(text.of(short, ""), text.of(long, "")))

# extras after the help string: default and choices
def help.extra.go(+dd: String, +cs: List<&2, String>) -> String:
  Bool.pick(String, String.is_empty(dd),
    Bool.pick(String, List.is_empty(&2, String, cs), "",
      " [possible values: " ++ String.join(cs, ", ") ++ "]"),
    Bool.pick(String, List.is_empty(&2, String, cs),
      " [default: " ++ dd ++ "]",
      " [default: " ++ dd ++ "] [possible values: " ++ String.join(cs, ", ") ++
        "]"))

# extras after the help string
def help.extra(aa: Arg) -> String:
  Arg{_n, _s, _l, _k, _h, _r, default, cs} = aa
  help.extra.go(text.of(default, ""), cs)

# one option line, given the label width
def help.opt_line(+aa: Arg, ww: Nat) -> String:
  Arg{_n, _s, _l, _k, +h, _r, _d, _c} = aa
  help.pad(help.label(aa), ww) ++ "  " ++ h ++ help.extra(aa)

# the max option-label width
def help.opt_width(args: List<&2, Arg>, nn: Nat) -> Nat:
  match args:
    case Nil{}:
      nn
    case Con{+h, t}:
      help.opt_width(t, help.max(nn, String.length(help.label(h))))

# a non-positional option line
def help.opt_lines.at(skip: Bool, hh: Arg, rest: String, ww: Nat) -> String:
  match skip:
    case True{}:
      rest
    case False{}:
      help.opt_line(hh, ww) ++ "\n" ++ rest

# option lines, skipping positionals
def help.opt_lines(args: List<&2, Arg>, +ww: Nat) -> String:
  match args:
    case Nil{}:
      ""
    case Con{+h, t}:
      help.opt_lines.at(pos.is(h), h, help.opt_lines(t, ww), ww)

# wrap option lines in a heading
def help.opts.go(+body: String) -> String:
  Bool.pick(String, String.is_empty(body), "", "Options:\n" ++ body ++ "\n")

# the Options block, or empty when there are none
def help.opts(+args: List<&2, Arg>) -> String:
  help.opts.go(help.opt_lines(args, help.opt_width(args, 0n)))

# a command's name
def help.sub_name(ss: Sub) -> String:
  Sub{n, _a, _g, _c} = ss
  n

# a command's about
def help.sub_about(ss: Sub) -> String:
  Sub{_n, a, _g, _c} = ss
  a

# max command-name width, including `help`
def help.cmd_width(subs: List<&2, Sub>, nn: Nat) -> Nat:
  match subs:
    case Nil{}:
      help.max(nn, String.length("help"))
    case Con{+h, t}:
      help.cmd_width(t, help.max(nn, String.length(help.sub_name(h))))

# one command line
def help.cmd_line(+name: String, +about: String, ww: Nat) -> String:
  "  " ++ help.pad(name, ww) ++ "  " ++ about ++ "\n"

# command lines, then `help`
def help.cmd_lines(subs: List<&2, Sub>, +ww: Nat) -> String:
  match subs:
    case Nil{}:
      help.cmd_line("help",
        "Print this message or the help of the given subcommand(s)", ww)
    case Con{+h, t}:
      help.cmd_line(help.sub_name(h), help.sub_about(h), ww) ++ help.cmd_lines(t, ww)

# the Commands block
def help.cmds(+subs: List<&2, Sub>) -> String:
  "Commands:\n" ++ help.cmd_lines(subs, help.cmd_width(subs, 0n)) ++ "\n"

# a rest mark: `...`, or empty
def help.pos.dots(many: Bool) -> String:
  Bool.pick(String, many, "...", "")

# a positional in a usage line: `<NAME>` or `[NAME]`
def help.pos.wrap(req: Bool, +nn: String) -> String:
  Bool.pick(String, req, " <" ++ nn ++ ">", " [" ++ nn ++ "]")

# a positional in a usage line: `<NAME>` or `[NAME]`, plus `...` when rest
def help.pos.one(aa: Arg) -> String:
  Arg{+n, _s, _l, kind, _h, +req, _d, _c} = aa
  help.pos.wrap(req, String.to_upper(n)) ++ help.pos.dots(rest.is.kind(kind))

# this positional's hint, else the rest
def help.pos.at(keep: Bool, hh: Arg, rest: String) -> String:
  match keep:
    case True{}:
      help.pos.one(hh) ++ rest
    case False{}:
      rest

# every positional in a usage line
def help.pos(args: List<&2, Arg>) -> String:
  match args:
    case Nil{}:
      ""
    case Con{+h, t}:
      help.pos.at(pos.is(h), h, help.pos(t))

# the bracketed options word when the spec has a flag or option
def help.opts_hint.go(has: Bool) -> String:
  Bool.pick(String, has, " [" ++ String.to_upper("options") ++ "]", "")

# True when this Arg is a flag or option, else the rest
def help.has_opt.at(is_pos: Bool, rest: Bool) -> Bool:
  match is_pos:
    case True{}:
      rest
    case False{}:
      True{}

# whether any Arg is not a positional
def help.has_opt(args: List<&2, Arg>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{+h, t}:
      help.has_opt.at(pos.is(h), help.has_opt(t))

# the options hint when needed
def help.opts_hint(args: List<&2, Arg>) -> String:
  help.opts_hint.go(help.has_opt(args))

# `[COMMAND]` when there are subcommands
def help.cmd_hint(+subs: List<&2, Sub>) -> String:
  Bool.pick(String, List.is_empty(&2, Sub, subs), "", " [COMMAND]")

# `Usage: name ...`
def help.usage(
  +name: String,
  +args: List<&2, Arg>,
  +subs: List<&2, Sub>
) -> String:
  "Usage: " ++ name ++ help.opts_hint(args) ++ help.pos(args) ++ help.cmd_hint(subs)

# `name` or `name version`
def title.go(+name: String, vv: Maybe<&2, String>) -> String:
  match vv:
    case None{}:
      name
    case Some{ver}:
      name ++ " " ++ ver

# one help page
def help.page(
  +title: String,
  +about: String,
  +usage: String,
  +args: List<&2, Arg>,
  +subs: List<&2, Sub>
) -> String:
  title ++ "\n" ++ about ++ "\n\n" ++ usage ++ "\n\n" ++ help.cmds(subs) ++
    help.opts(args)

# a found child becomes the page; an unknown name stays
def help.step.go(
  found: Maybe<&2, Sub>,
  +bin: String,
  +about: String,
  version: Maybe<&2, String>,
  args: List<&2, Arg>,
  subs: List<&2, Sub>,
  +next: String,
  +usage: String
) -> How:
  match found:
    case None{}:
      How{bin, about, version, args, subs, usage}
    case Some{s}:
      Sub{+name, +about2, args2, subs2} = s
      How{name, about2, None{}, args2, subs2, usage ++ " " ++ next}

# one path segment against the current page
def help.step(how: How, +name: String) -> How:
  How{+bin, +about, version, args, +subs, +usage} = how
  help.step.go(find_sub(subs, name), bin, about, version, args, subs, name,
    usage)

# the page at the end of a shrinking path
def help.go(path: List<&2, String>, how: How) -> String:
  match path:
    case Nil{}:
      How{+bin, +about, version, +args, +subs, +usage} = how
      help.page(title.go(bin, version), about, help.usage(usage, args, subs),
        args, subs)
    case Con{+h, t}:
      help.go(t, help.step(how, h))

# usage for `path` under `app`; an unknown segment shows the last found page
def help(+app: Cli, path: List<&2, String>) -> String:
  Cli{+name, +about, version, args, subs} = app
  help.go(path, How{name, about, version, args, subs, name})

# a short error with the root usage line
def err.wrap(app: Cli, +msg: String) -> String:
  Cli{+name, _a, _v, args, subs} = app
  msg ++ "\n\n" ++ help.usage(name, args, subs) ++
    "\n\nFor more information, try 'help'.\n"

# error text; NeedHelp is empty (the caller prints `help`)
def err_text(+app: Cli, ee: ParseErr) -> String:
  match ee:
    case UnknownFlag{word}:
      err.wrap(app, "error: unexpected argument '" ++ word ++ "' found")
    case Missing{name}:
      err.wrap(app, "error: the following required argument was not provided:\n  " ++
        name)
    case BadValue{name, value}:
      err.wrap(app, "error: invalid value '" ++ value ++ "' for '" ++ name ++ "'")
    case NeedHelp{_path}:
      ""
    case Unexpected{arg}:
      err.wrap(app, "error: unexpected argument '" ++ arg ++ "' found")
