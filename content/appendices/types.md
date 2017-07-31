This file describes the main types used in the implementation of HOL Light.

`lib.ml`:
```ocaml
type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;
```
The representation of finite partial functions.


`fusion.ml`:
```ocaml
type hol_type =
  Tyvar of string
| Tyapp of string *  hol_type list
```

```ocaml
type term =
  Var of string * hol_type
| Const of string * hol_type
| Comb of term * term
| Abs of term * term
```

```ocaml
type thm = Sequent of (term list * term)
```


`nets.ml`:
```ocaml
type term_label =
  Vnet                         (* variable (instantiable)   *)
| Lcnet of (string * int)      (* local constant            *)
| Cnet of (string * int)       (* constant                  *)
| Lnet of int                  (* lambda term (abstraction) *)
```

```ocaml
type 'a net = Netnode of (term_label * 'a net) list * 'a list
```
Term nets are a finitely branching tree structure; at each level we have a set
of branches and a set of 'values'.  Linearisation is performed from the left of
a combination; even in iterated combinations we look at the head first.  This
is probably fastest, and anyway it's useful to allow our restricted second
order matches:  if the head is a variable then then whole term is treated as a
variable.


`preterm.ml`:
107:type pretype = Utv of string                   (* User type variable         *)
130:type preterm = Varp of string * pretype       (* Variable           - v      *)

`parser.ml`:
88:type lexcode = Ident of string

`equal.ml`:
16:type conv = term->thm;;

`drule.ml`:
16:type instantiation =

`tactics.ml`:
25:type goal = (string * thm) list * term;;
38:type justification = instantiation -> thm list -> thm;;
45:type goalstate = (term list * instantiation) * goal list * justification;;
51:type goalstack = goalstate list;;
59:type refinement = goalstate -> goalstate;;
71:type tactic = goal -> goalstate;;
73:type thm_tactic = thm -> tactic;;
75:type thm_tactical = thm_tactic -> thm_tactic;;


`simp.ml`:
16:type gconv = int * conv;;
194:type prover = Prover of conv * (thm list -> prover);;
217:type simpset =

`impconv.ml`:
738:type imp_conv = Variance.t -> term -> thm
805:type 'a with_context =
1072:type atomic = Atomic | Non_atomic
1171:type annot_conv = term -> thm * term option * term list
1438:type imp_mconv = Variance.t -> term -> thm list
1607:type annot_mconv = term -> (thm * term option * term list) list

`grobner.ml`:
19:type history =

`realarith.ml`:
153:type positivstellensatz =
