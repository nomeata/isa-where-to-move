Where should I put this lemma?
==============================

I usually work with many Isabelle theories, which form a DAG, and generally I
want auxillary lemmas to be proven as early as possible.

Disclaimer
----------

This builds on infrastructure in Isabelle of which it is said that
[“None of this really works,
though.”](https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2014-December/msg00076.html).
Furthermore, I am not an experienced Isabelle programmer, so what I’m doing
might be wrong, inefficient and/or stupid. Use at your own risk (and/or submit
patches!).


Motivation
----------

Consider these four files:

    theory Where_To_Move_Ex1
    imports Main
    begin

    definition "foo = True"

    lemma fooI: foo unfolding foo_def..

    end



    theory Where_To_Move_Ex2
    imports Main
    begin

    definition "bar = False"

    lemma barE: "bar ==> P" unfolding bar_def by (erule FalseE)

    end


    theory Where_To_Move_Ex3
    imports Where_To_Move_Ex1 Where_To_Move_Ex2
    begin
    (* nothing here yet *)
    end


    theory Where_To_Move_Ex4
    imports Where_To_Move_Ex3 WhereToMove
    begin

    lemma fooI2: "foo" by (rule fooI)
    lemma barE2: "bar \<Longrightarrow> P" by (rule barE)
    lemma foobar: "foo \<and> \<not> bar"
      apply rule
      apply (rule fooI)
      apply (rule notI)
      apply (erule barE)
      done
    lemma foobar2: "foo \<and> \<not> bar"
      apply rule
      apply (rule fooI2)
      apply (rule notI)
      apply (erule barE2)
      done

    end

Seening this, my usual thoughts would be

 * `fooI2` could just as well go to `Where_To_Move_Ex1` directly; it uses
   nothing from the other theories.
 * Similarly, `barE2` should go to `Where_To_Move_Ex2`.
 * `foobar` cannot go to either `Where_To_Move_Ex1` nor `Where_To_Move_Ex2`. But it still
   is not at a proper spot right now: The theory `Where_To_Move_Ex3` is more suitable.
 * `foobar2` is, upon first glance, at the right spot, as it uses `fooI2` and
   `barE2` from this module. *If* I would move `fooI2` and `barE2`, I would also be
   able to move `foobar2`, but maybe I will not do that, so for now `foobar2`
   stays where it is.

Example use
-----------

If I enter the command `where_to_move` at the end of the theory
`Where_To_Move_Ex4`, I will be given this somewhat helpful output:

    Theorem Where_To_Move_Ex4.barE2 could be moved to theory "Where_To_Move_Ex2".
    Theorem Where_To_Move_Ex4.fooI2 could be moved to theory "Where_To_Move_Ex1".
    Theorem Where_To_Move_Ex4.foobar could be moved to theory "Where_To_Move_Ex3".

The output did not mention `foobar2`, but if I expliclty ask for it to be
checked using `where_to_move foobar2` I get

    Theorem Where_To_Move_Ex4.foobar2 is fine where it is.

Installation
------------

 * Clone this repository somewhere, say to `~/isabelle/isa-where-to-move`.
 * Add `"$HOME/isabelle/isa-where-to-move/Where_To_Move"` to your import list
 * Done

Usage
-----

 * `where_to_move`

   For all lemmas defined in the current module, give an indication where it should be
   moved.

   The logic is as follows: In the list of dependencies of the current theory,
   find the first (i.e. most primitive) theory that already contains all
   constants occurring in the theorem, and all lemmas occurring in its proof.

 * `where_to_move` *thm*

   The same, but for a specific theorem only.

 * `theorems_used_by` *thm*

   Prints all theorems used by the given theorems. Can be useful to understand
   why `where_to_move` suggests a particular choice.

 * `constants_used_by` *thm*

   Prints all constants occuring in a given theorem.


Bugs and shortcomings
---------------------

These are the ones that I know about. If you have more, feel free to open an issue.

 * In the output of `theorems_used_by`, if a theorem is actually a list of
   them, and one is used, it prints the selector as part of the name
   (`HOL.simp_thms_7`), which breaks the hyperlinking.
 * It might suggest moving a theorem that mentions a type from the current
   theory (but no lemma or constant) to another theory.
 * It is confused by interpretations, and may suggest moving interpreted lemmas.
 * Typing commands is an out-dated interface. Ideally, after activating this tool,
   every proven lemma would be checked in the background and some wiggly lines would
   indicate that this lemma could live somewhere else, similar to how `solve_direct` and
   `nitpick` are run automatically.
 * The installation suggestions make you enter the full path to the theory file
   everytime you use it. Maybe it is possible to avoid this by registering this as
   an *component*, but I could not make that work right away.
 * The ML code could use some code review from someone more experienced with
   SML and Isabelle/ML.

