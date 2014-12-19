(*  Title: where_to_move.ML
    Author: Joachim Breitner

Utility commands to suggest lemma reorganisations.
*)

signature WHERE_TO_MOVE =
sig
  val thms_used_by_thm : thm -> string list
  val constants_used_by_thm : thm -> string list
  val theories_used_by_thm : theory -> thm -> theory list
  val theories_used_by_thms : theory -> thm list -> theory list

  val constants_used_by_cmd : (string * Position.T) -> Toplevel.transition -> Toplevel.transition
  val theorems_used_by_cmd : (string * Position.T) -> Toplevel.transition -> Toplevel.transition
  val where_to_move_cmd : (string * Position.T) list option -> Toplevel.transition -> Toplevel.transition
end

structure Where_To_Move : WHERE_TO_MOVE =
struct

fun thms_used_by_thm thm =
  let
  fun  used_by_proof_body (PBody {thms, ...}) = thms |> map #2 |> maps go
  and go ("", _, pbodyf) = pbodyf |> Future.join |> used_by_proof_body
    | go (s, _, _) = [s]
  in thm |> Thm.proof_body_of |> Proofterm.strip_thm |> used_by_proof_body
  end;

fun constants_used_by_thm thm =
  let val term = Thm.prop_of thm
      val consts = Term.add_const_names term []
  in consts
  end;

fun nub ss = fold (fn x => Symtab.update (x, ())) ss Symtab.empty |> Symtab.keys;

fun theories_used_by_thms thy thm =
  let val thms = maps thms_used_by_thm thm
      val consts = maps constants_used_by_thm thm
      val theory_names = thms @ consts |> map (hd o Long_Name.explode) |> nub
      val theories = theory_names |> map (Context.this_theory thy) 
  in theories
  end

fun theories_used_by_thm thy thm = theories_used_by_thms thy [thm]


fun ok_for thys thy =
  forall (fn thy' => 
    let (* val _ = writeln (@{make_string} (theory_name thy', theory_name  thy,  Context.subthy (thy', thy))) *)
    in  Context.subthy (thy', thy) end) thys

fun better_theory thys this_thy =
  Context.ancestors_of this_thy 
  |> rev (* this way we get a minimal solution *)
  |> find_first  (ok_for thys);


fun pretty_fact ctxt name =
  Pretty.mark (#1 (Proof_Context.markup_extern_fact ctxt name)) (Pretty.str name)

fun theorems_used_by_cmd arg = Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state
        val thy = Toplevel.theory_of state
        val (_, thms) =  Facts.retrieve (Context.Proof ctxt) (Global_Theory.facts_of thy) arg
    in thms |> maps thms_used_by_thm
            |> map (pretty_fact ctxt)
            |> Pretty.commas
            |> Pretty.paragraph
            |> Pretty.writeln
    end
    );


fun pretty_const ctxt c =
  let
    val const_space = Consts.space_of (Sign.consts_of (Proof_Context.theory_of ctxt));
    val markup = Name_Space.markup const_space c;
  in
    Pretty.mark markup (Pretty.str c)
  end;

fun constants_used_by_cmd arg = Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state
        val thy = Toplevel.theory_of state
        val (_, thms) =  Facts.retrieve (Context.Proof ctxt) (Global_Theory.facts_of thy) arg
    in thms |> maps constants_used_by_thm
            |> map (pretty_const ctxt)
            |> Pretty.commas
            |> Pretty.paragraph
            |> Pretty.writeln
    end
    );


fun facts_of_theory thy =
  let val prev_thys = (Theory.parents_of thy) 
      val facts = Global_Theory.facts_of thy
      val thms =  Facts.dest_static false (map Global_Theory.facts_of prev_thys) facts
  in thms end;


fun where_to_move_cmd args_o =
  Toplevel.keep ( fn state =>
    let val ctxt = Toplevel.context_of state
        val this_thy = Toplevel.theory_of state
        val (verbose, named_thms) = case args_o of
            SOME args => (true, args |> map (Facts.retrieve (Context.Proof ctxt) (Global_Theory.facts_of this_thy)))
            | NONE =>    (false, facts_of_theory this_thy)
    in named_thms |> map (fn (name, thms) =>
      let val pretty_name = name |> pretty_fact ctxt |> Pretty.quote
          val current_thy_name = name |> (hd o Long_Name.explode)
          val current_thy = Context.this_theory this_thy current_thy_name
      in case better_theory (theories_used_by_thms this_thy thms) current_thy of
          SOME thy =>
           [ Pretty.str "Theorem ", pretty_name,
             Pretty.str " could be moved to theory ",
             Pretty.quote (Pretty.mark_str (Theory.get_markup thy, Context.theory_name thy)),
             Pretty.str "."
           ] |> Pretty.paragraph |> Pretty.writeln
        | NONE =>
          if verbose then
           [ Pretty.str "Theorem ", pretty_name,
             Pretty.str" is fine where it is."] |> Pretty.paragraph |> Pretty.writeln
          else ()
      end
    ) |> K ()
   end
   );


val _ = Outer_Syntax.improper_command @{command_spec "theorems_used_by"} 
    "prints all theorems used by the given theorem"
    (Parse.position Parse.xname >> theorems_used_by_cmd);

val _ = Outer_Syntax.improper_command @{command_spec "constants_used_by"} 
    "prints all constants occurring in the given theorem"
    (Parse.position Parse.xname >> constants_used_by_cmd);

val _ = Outer_Syntax.improper_command @{command_spec "where_to_move"}
    "suggests a new location for the given theorem or, of none is given, all theorems in the current theory"
    (Scan.option (Scan.repeat1 (Parse.position Parse.xname)) >> where_to_move_cmd);

end
