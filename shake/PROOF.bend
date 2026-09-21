# shake: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./LAWS.bend as Laws

def Laws.app_is_cli(_name, _about, _version, _args, _subs):
  {==}

def Laws.sub_is_sub(_name, _about, _args, _subs):
  {==}

def Laws.flag_is_arg(_name, _short, _long, _help):
  {==}

def Laws.opt_is_arg(_name, _short, _long, _help, _required, _default, _choices):
  {==}

def Laws.pos_is_arg(_name, _help, _required, _default, _choices):
  {==}

def Laws.rest_is_arg(_name, _help, _required, _default, _choices):
  {==}

def Laws.looks_flag_is_dash(_s):
  {==}

def Laws.looks_flag_long(_s):
  {==}

def Laws.looks_flag_alone(_u):
  {==}

def Laws.cut_eq_is_go(_s):
  {==}

def Laws.cut_eq_plain(_u):
  {==}

def Laws.cut_eq_value(_u):
  {==}

def Laws.short_of_is_take(_s):
  {==}

def Laws.short_of_glued(_u):
  {==}

def Laws.short_of_one(_u):
  {==}

def Laws.by_long_nil(_name):
  {==}

def Laws.by_long_flag(_u):
  {==}

def Laws.by_short_nil(_name):
  {==}

def Laws.by_short_flag(_u):
  {==}

def Laws.by_name_nil(_name):
  {==}

def Laws.by_name_flag(_u):
  {==}

def Laws.find_sub_nil(_name):
  {==}

def Laws.find_sub_head(_u):
  {==}

def Laws.pos_of_nil(_u):
  {==}

def Laws.pos_of_keeps(_u):
  {==}

def Laws.pos_of_rest(_u):
  {==}

def Laws.rest_last_none(_u):
  {==}

def Laws.rest_last_ok(_u):
  {==}

def Laws.rest_last_mid(_u):
  {==}

def Laws.allowed_any(_v):
  {==}

def Laws.allowed_listed(_u):
  {==}

def Laws.allowed_other(_u):
  {==}

def Laws.bound_nil(_name):
  {==}

def Laws.bound_head(_u):
  {==}

def Laws.get_nil(_name):
  {==}

def Laws.get_head(_u):
  {==}

def Laws.get_all_nil(_name):
  {==}

def Laws.get_all_two(_u):
  {==}

def Laws.on_nil(_name):
  {==}

def Laws.on_true(_u):
  {==}

def Laws.path_of_keeps(_path, _binds):
  {==}

def Laws.parse_is_walk(_app, _argv):
  {==}

def Laws.show_done(_m):
  {==}

def Laws.show_fail(_e):
  {==}

def Laws.help_is_go(_name, _about, _version, _args, _subs, _path):
  {==}

def Laws.err_text_help(_app, _path):
  {==}

def Laws.parse_flag_long(_u):
  {==}

def Laws.parse_flag_short(_u):
  {==}

def Laws.parse_opt_long(_u):
  {==}

def Laws.parse_opt_eq(_u):
  {==}

def Laws.parse_opt_short(_u):
  {==}

def Laws.parse_opt_glued(_u):
  {==}

def Laws.parse_pos(_u):
  {==}

def Laws.parse_default(_u):
  {==}

def Laws.parse_add(_u):
  {==}

def Laws.parse_nested(_u):
  {==}

def Laws.parse_dash(_u):
  {==}

def Laws.err_missing(_u):
  {==}

def Laws.err_choice(_u):
  {==}

def Laws.err_unknown_long(_u):
  {==}

def Laws.err_unknown_short(_u):
  {==}

def Laws.err_help_root(_u):
  {==}

def Laws.err_help_greet(_u):
  {==}

def Laws.err_unexpected(_u):
  {==}

def Laws.parse_rest_none(_u):
  {==}

def Laws.parse_rest_one(_u):
  {==}

def Laws.parse_rest_many(_u):
  {==}

def Laws.parse_rest_dash(_u):
  {==}

def Laws.err_rest_missing(_u):
  {==}

def Laws.show_rest_many(_u):
  {==}

def Laws.help_root(_u):
  {==}

def Laws.help_greet(_u):
  {==}

def Laws.help_add(_u):
  {==}

def Laws.help_rest(_u):
  {==}

def Laws.help_rest_req(_u):
  {==}

def Laws.err_text_unknown(_u):
  {==}

def Laws.copy_nil(_u):
  {==}

def Laws.copy_one(_h):
  {==}

def Laws.argv_is_copy(_u):
  {==}
