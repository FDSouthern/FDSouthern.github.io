---
title: simp.ml
---

[Original file](https://github.com/jrh13/hol-light/blob/master/simp.ml)

Simplification and rewriting.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Generalized conversion (conversion plus a priority).                      *)
(* ------------------------------------------------------------------------- *)

type gconv = int * conv;;

(* ------------------------------------------------------------------------- *)
(* Primitive rewriting conversions: unconditional and conditional equations. *)
(* ------------------------------------------------------------------------- *)
```
A conditional rewrite is a conversion which produces a theorem
of the form `|- P ==> (a = b)`.  This rewrites `a` to `b` under
the condition `P`.  Previous conversionals cannot deal with conditional
rewrites.

```ocaml
let REWR_CONV = PART_MATCH lhs;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWR_CONV.html>

`` REWR_CONV `|- a = b` `` is a conversion which rewrites `a'` to `b'`.

```ocaml
let IMP_REWR_CONV = PART_MATCH (lhs o snd o dest_imp);;

```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/IMP_REWR_CONV.html>

`` IMP_REWR_CONV `A |- p ==> (s = t)` `` returns a conversion which matches
a term `s'` to `s` and returns the theorem `A |- p ==> (s' = t')`.

```ocaml

(* ------------------------------------------------------------------------- *)
(* Versions with ordered rewriting. We must have l' > r' for the rewrite     *)
(* |- l = r (or |- c ==> (l = r)) to apply.                                  *)
(* ------------------------------------------------------------------------- *)

let ORDERED_REWR_CONV ord th =
  let basic_conv = REWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(concl thm) in
    if ord l r then thm
    else failwith "ORDERED_REWR_CONV: wrong orientation";;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ORDERED_REWR_CONV.html>

`` ORDERED_REWR_CONV ord `|- a = b` `` is a conversion which rewrites `a'` to
`b'` if `` (ord `a'` `b'`) ``, otherwise it fails.

```ocaml
let ORDERED_IMP_REWR_CONV ord th =
  let basic_conv = IMP_REWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(rand(concl thm)) in
    if ord l r then thm
    else failwith "ORDERED_IMP_REWR_CONV: wrong orientation";;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ORDERED_IMP_REWR_CONV.html>

`` ORDERED_IMP_REWR_CONV ord `|- P ==> (a = b)` `` is a conversion which
rewrites `a@` to `b@` under the condition `P@` if `` (ord `a@` `b@`) ``.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Standard AC-compatible term ordering: a "dynamic" lexicographic ordering. *)
(*                                                                           *)
(* This is a slight hack to make AC normalization work. However I *think*    *)
(* it's properly AC compatible, i.e. monotonic and total, WF on ground terms *)
(* (over necessarily finite signature) and with the properties for any       *)
(* binary operator +:                                                        *)
(*                                                                           *)
(*         (x + y) + z > x + (y + z)                                         *)
(*         x + y > y + x                   iff x > y                         *)
(*         x + (y + z) > y + (x + z)       iff x > y                         *)
(*                                                                           *)
(* The idea is that when invoking lex ordering with identical head operator  *)
(* "f", one sticks "f" at the head of an otherwise arbitrary ordering on     *)
(* subterms (the built-in CAML one). This avoids the potentially inefficient *)
(* calculation of term size in the standard orderings.                       *)
(* ------------------------------------------------------------------------- *)

let term_order =
  let rec lexify ord l1 l2 =
    if l1 = [] then false
    else if l2 = [] then true else
    let h1 = hd l1 and h2 = hd l2 in
    ord h1 h2 || (h1 = h2 && lexify ord (tl l1) (tl l2)) in
  let rec dyn_order top tm1 tm2 =
    let f1,args1 = strip_comb tm1
    and f2,args2 = strip_comb tm2 in
    if f1 = f2 then
      lexify (dyn_order f1) args1 args2
    else
      if f2 = top then false
      else if f1 = top then true
      else f1 > f2 in
  dyn_order `T`;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/term_order.html>

`term_order` is an ordering function which is AC-compatible for any binary
operator.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a theorem as a (cond) rewrite. The "rep" flag      *)
(* will cause any trivially looping rewrites to be modified, and any that    *)
(* are permutative to be ordered w.r.t. the standard order. The idea is that *)
(* this flag will be set iff the conversion is going to get repeated.        *)
(* This includes a completely ad hoc but useful special case for ETA_AX,     *)
(* which forces a first order match (otherwise it would loop on a lambda).   *)
(* ------------------------------------------------------------------------- *)

let net_of_thm rep th =
  let tm = concl th in
  let lconsts = freesl (hyp th) in
  let matchable = can o term_match lconsts in
  match tm with
    Comb(Comb(Const("=",_),(Abs(x,Comb(Var(s,ty) as v,x')) as l)),v')
         when x' = x && v' = v && not(x = v) ->
        let conv tm =
          match tm with
            Abs(y,Comb(t,y')) when y = y' && not(free_in y t) ->
              INSTANTIATE(term_match [] v t) th
          | _ -> failwith "REWR_CONV (ETA_AX special case)" in
        enter lconsts (l,(1,conv))
  | Comb(Comb(Const("=",_),l),r) ->
      if rep && free_in l r then
        let th' = EQT_INTRO th in
        enter lconsts (l,(1,REWR_CONV th'))
      else if rep && matchable l r && matchable r l then
        enter lconsts (l,(1,ORDERED_REWR_CONV term_order th))
      else enter lconsts (l,(1,REWR_CONV th))
  | Comb(Comb(_,t),Comb(Comb(Const("=",_),l),r)) ->
        if rep && free_in l r then
          let th' = DISCH t (EQT_INTRO(UNDISCH th)) in
          enter lconsts (l,(3,IMP_REWR_CONV th'))
        else if rep && matchable l r && matchable r l then
          enter lconsts (l,(3,ORDERED_IMP_REWR_CONV term_order th))
        else enter lconsts(l,(3,IMP_REWR_CONV th));;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/net_of_thm.html>

`` net_of_thm rep `|- P ==> (a = b)` (or `|- a = b`) net `` adds a component to
`net` which matches a term and returns a conversion rewriting that term.
If rep is true and `a` appears in `b`, then it rewrites `(a = b)` to `T`.
If rep is true and the rewrite is permutative, then it uses an
ordered rewrite to rewrite `a` to `b`.
If neither of the above is true, then it uses an ordinary rewrite.
Conditional rewrites are entered as level 3; unconditional as level 1.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a conversion with a term index.                    *)
(* ------------------------------------------------------------------------- *)

let net_of_conv tm conv sofar =
  enter [] (tm,(2,conv)) sofar;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/net_of_conv.html>

`net_of_conv tm conv net` adds a component to `net` which matches `tm` and
returns `conv`.  Entered as level 2.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a congruence rule (in canonical form!)             *)
(* ------------------------------------------------------------------------- *)

let net_of_cong th sofar =
  let conc,n = repeat (fun (tm,m) -> snd(dest_imp tm),m+1) (concl th,0) in
  if n = 0 then failwith "net_of_cong: Non-implicational congruence" else
  let pat = lhs conc in
  let conv = GEN_PART_MATCH (lhand o funpow n rand) th in
  enter [] (pat,(4,conv)) sofar;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/net_of_cong.html>

`net_of_cong th net` adds a component to `net` for a congruence rule (a rule of
the form `` `P1 ==> (P2 ==> (...(Pn ==> (a = b))))` ``).  Entered at level 4.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Rewrite maker for ordinary and conditional rewrites (via "cf" flag).      *)
(*                                                                           *)
(* We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F.    *)
(* Well, why not? However, we don't abandon s = t where FV(t) is not a       *)
(* subset of FV(s) in favour of (s = t) = T, as he does.                     *)
(* Note: looping rewrites are not discarded here, only when netted.          *)
(* ------------------------------------------------------------------------- *)

let mk_rewrites =
  let IMP_CONJ_CONV = REWR_CONV(ITAUT `p ==> q ==> r <=> p /\ q ==> r`)
  and IMP_EXISTS_RULE =
    let cnv = REWR_CONV(ITAUT `(!x. P x ==> Q) <=> (?x. P x) ==> Q`) in
    fun v th -> CONV_RULE cnv (GEN v th) in
  let collect_condition oldhyps th =
    let conds = subtract (hyp th) oldhyps in
    if conds = [] then th else
    let jth = itlist DISCH conds th in
    let kth = CONV_RULE (REPEATC IMP_CONJ_CONV) jth in
    let cond,eqn = dest_imp(concl kth) in
    let fvs = subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps) in
    itlist IMP_EXISTS_RULE fvs kth in
  let rec split_rewrites oldhyps cf th sofar =
    let tm = concl th in
    if is_forall tm then
      split_rewrites oldhyps cf (SPEC_ALL th) sofar
    else if is_conj tm then
      split_rewrites oldhyps cf (CONJUNCT1 th)
        (split_rewrites oldhyps cf (CONJUNCT2 th) sofar)
    else if is_imp tm && cf then
      split_rewrites oldhyps cf (UNDISCH th) sofar
    else if is_eq tm then
      (if cf then collect_condition oldhyps th else th)::sofar
    else if is_neg tm then
      let ths = split_rewrites oldhyps cf (EQF_INTRO th) sofar in
      if is_eq (rand tm)
      then split_rewrites oldhyps cf (EQF_INTRO (GSYM th)) ths
      else ths
    else
      split_rewrites oldhyps cf (EQT_INTRO th) sofar in
  fun cf th sofar -> split_rewrites (hyp th) cf th sofar;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/mk_rewrites.html>

`mk_rewrites cf th rew_list` prepends rewrites for `th` to `new_list`.
I will describe the action in terms of a notional `add_rew` function:

```
(add_rew l `|- !x. P[x]`) --> (add_rew l `|- P[x]`)
(add_rew l `|- P1 /\ P2`) --> (add_rew l `|- P1`), (add_rew l `|- P2`)
if cf, then (add_rew l `|- P1 ==> P2`) --> (add_rew (`P1`::l) `|- P2`)
(add_rew l `|- a = b`) adds a conditional rewrite with conditions l
         (if l is empty, this is an unconditional rewrite;
         if cf is false, then l is always empty)
(add_rew l `|- ~(a = b)`) --> (add_rew l `|- (a = b) = F`), (add_rew l `|- (b = a) = F`)
(add_rew l `|- ~a`) --> (add_rew l `|- a = F`)
```
If none of the above hold, `` (add_rew l `|- a`) --> (add_rew l `|- a = T`) ``.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Rewriting (and application of other conversions) based on a convnet.      *)
(* ------------------------------------------------------------------------- *)

let REWRITES_CONV net tm =
  let pconvs = lookup tm net in
  try tryfind (fun (_,cnv) -> cnv tm) pconvs
  with Failure _ -> failwith "REWRITES_CONV";;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITES_CONV.html>

`` REWRITES_CONV net `a` `` looks up `a` in the net, and applies the resulting
conversion to `a`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Decision procedures may accumulate their state in different ways (e.g.    *)
(* term nets and predicate-indexed lists of Horn clauses). To allow mixing   *)
(* of arbitrary types for state storage, we use a trick due to RJB via DRS.  *)
(* ------------------------------------------------------------------------- *)

type prover = Prover of conv * (thm list -> prover);;

let mk_prover applicator augmentor =
  let rec mk_prover state =
    let apply = applicator state
    and augment thms = mk_prover (augmentor state thms) in
    Prover(apply,augment) in
  mk_prover;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/mk_prover.html>

```ocaml
let augment(Prover(_,aug)) thms = aug thms;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/augment.html>

```ocaml
let apply_prover(Prover(conv,_)) tm = conv tm;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/apply_prover.html>

```ocaml
(* ------------------------------------------------------------------------- *)
(* Type of simpsets. We have a convnet containing rewrites (implicational    *)
(* and otherwise), other term-indexed context-free conversions like          *)
(* BETA_CONV, and congruence rules. Then there is a list of provers that     *)
(* have their own way of storing and using context, and finally a rewrite    *)
(* maker function, to allow customization.                                   *)
(*                                                                           *)
(* We also have a type of (traversal) strategy, following Konrad.            *)
(* ------------------------------------------------------------------------- *)

type simpset =
  Simpset of gconv net                          (* Rewrites & congruences *)
           * (strategy -> strategy)             (* Prover for conditions  *)
           * prover list                        (* Subprovers for prover  *)
           * (thm -> thm list -> thm list)      (* Rewrite maker          *)

and strategy = simpset -> int -> term -> thm;;
```
There's a lot of generality in the simpset data structure which is not
used; I'm not going to try to understand the general-purpose operation,
but only the portions of it which are actually used in HOL Light.
Of the four fields in the simpset data structure, only the first ever
changes: the second is always `basic_prover`, the third is always the
empty list, and the fourth is always `(mk_rewrites true)`.
The first field is a conversion net.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Very simple prover: recursively simplify then try provers.                *)
(* ------------------------------------------------------------------------- *)

let basic_prover strat (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
  let sth = try strat ss lev tm with Failure _ -> REFL tm in
  try EQT_ELIM sth
  with Failure _ ->
    let tth = tryfind (fun pr -> apply_prover pr (rand(concl sth))) provers in
    EQ_MP (SYM sth) tth;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_prover.html>

`` basic_prover strat ss lev `a` `` tries to prove `|- a`.
Succeeds if `a` = `T`, or if `` (strat ss lev `a`) `` proves `|- a = T`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Functions for changing or augmenting components of simpsets.              *)
(* ------------------------------------------------------------------------- *)

let ss_of_thms thms (Simpset(net,prover,provers,rewmaker)) =
  let cthms = itlist rewmaker thms [] in
  let net' = itlist (net_of_thm true) cthms net in
  Simpset(net',prover,provers,rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_thms.html>

`ss_of_thms thms ss` augments a simpset with a list of theorems using the
rewrite maker from the simpset to add the theorems to the conversion net.

```ocaml
let ss_of_conv keytm conv (Simpset(net,prover,provers,rewmaker)) =
  let net' = net_of_conv keytm conv net in
  Simpset(net',prover,provers,rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_conv.html>

`ss_of_conv keytm conv ss` augments a simpset with a conversion using
`(net_of_conv keytm conv)` to add the conversion to the conversion net.

```ocaml
let ss_of_congs thms (Simpset(net,prover,provers,rewmaker)) =
  let net' = itlist net_of_cong thms net in
  Simpset(net',prover,provers,rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_congs.html>

```ocaml
let ss_of_prover newprover (Simpset(net,_,provers,rewmaker)) =
  Simpset(net,newprover,provers,rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_prover.html>

`ss_of_prover newprover ss` replaces the prover in the simpset with `newprover`.

```ocaml
let ss_of_provers newprovers (Simpset(net,prover,provers,rewmaker)) =
  Simpset(net,prover,newprovers@provers,rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_provers.html>

`ss_of_provers newprovers ss` prepends `newprovers` to the list of subprovers in
the simpset.

```ocaml
let ss_of_maker newmaker (Simpset(net,prover,provers,_)) =
  Simpset(net,prover,provers,newmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ss_of_maker.html>

`ss_of_maker newmaker ss` replaces the rewrite maker in the simpset with
`newmaker`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Perform a context-augmentation operation on a simpset.                    *)
(* ------------------------------------------------------------------------- *)

let AUGMENT_SIMPSET cth (Simpset(net,prover,provers,rewmaker)) =
  let provers' = map (C augment [cth]) provers in
  let cthms = rewmaker cth [] in
  let net' = itlist (net_of_thm true) cthms net in
  Simpset(net',prover,provers',rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/AUGMENT_SIMPSET.html>

`AUGMENT_SIMPSET th ss` uses the rewrite maker from the simpset
`(always (mk_rewrites true))` to create a list of rewrite theorems from `th`;
and uses `(net_of_thm true)` to add these theorems to the conversion net in the
simpset.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)
```
Note: `IMP_REWRITES_CONV` and `GEN_SUB_CONV` have a different signature than
what I am documenting.  I will first describe the meaning of these functions,
then I will describe their implementation.

`IMP_REWRITES_CONV strat ss lev` is a conversion which looks up the term in the
ss conversion net.  It tries unconditional rewrites before conditional rewrites.
It will only accept a conditional rewrite if `strat ss (lev-1)` can rewrite the
condition to `T`.

`GEN_SUB_CONV strat ss lev` rewrites combinations and abstractions in a
depth-first manner by calling `strat ss lev` on subterms.  It has special
handling for if-then-else and implications; it adds the condition to the simpset
before simplifying the rest of the expression.

Both of these functions fail if they perform no rewrites.

```ocaml
let ONCE_DEPTH_SQCONV,DEPTH_SQCONV,REDEPTH_SQCONV,
    TOP_DEPTH_SQCONV,TOP_SWEEP_SQCONV =
  let IMP_REWRITES_CONV strat (Simpset(net,prover,provers,rewmaker) as ss) lev
                        pconvs tm =
    tryfind (fun (n,cnv) ->
      if n >= 4 then fail() else
      let th = cnv tm in
      let etm = concl th in
      if is_eq etm then th else
      if lev <= 0 then failwith "IMP_REWRITES_CONV: Too deep" else
      let cth = prover strat ss (lev-1) (lhand etm) in
      MP th cth) pconvs in
  let rec RUN_SUB_CONV strat ss lev triv th =
    let tm = concl th in
    if is_imp tm then
      let subtm = lhand tm in
      let avs,bod = strip_forall subtm in
      let (t,t'),ss',mk_fun =
        try dest_eq bod,ss,I with Failure _ ->
        let cxt,deq = dest_imp bod in
        dest_eq deq,AUGMENT_SIMPSET (ASSUME cxt) ss,DISCH cxt in
      let eth,triv' = try strat ss' lev t,false with Failure _ -> REFL t,triv in
      let eth' = GENL avs (mk_fun eth) in
      let th' = if is_var t' then INST [rand(concl eth),t'] th
                else GEN_PART_MATCH lhand th (concl eth') in
      let th'' = MP th' eth' in
      RUN_SUB_CONV strat ss lev triv' th''
    else if triv then fail() else th in
  let GEN_SUB_CONV strat ss lev pconvs tm =
    try tryfind (fun (n,cnv) ->
          if n < 4 then fail() else
          let th = cnv tm in
          RUN_SUB_CONV strat ss lev true th) pconvs
    with Failure _ ->
        if is_comb tm then
          let l,r = dest_comb tm in
          try let th1 = strat ss lev l in
              try let th2 = strat ss lev r in MK_COMB(th1,th2)
              with Failure _ -> AP_THM th1 r
          with Failure _ -> AP_TERM l (strat ss lev r)
        else if is_abs tm then
          let v,bod = dest_abs tm in
          let th = strat ss lev bod in
          try ABS v th with Failure _ ->
          let gv = genvar(type_of v) in
          let gbod = vsubst[gv,v] bod in
          let gth = ABS gv (strat ss lev gbod) in
          let gtm = concl gth in
          let l,r = dest_eq gtm in
          let v' = variant (frees gtm) v in
          let l' = alpha v' l and r' = alpha v' r in
          EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth
        else failwith "GEN_SUB_CONV" in
  let rec ONCE_DEPTH_SQCONV
       (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try IMP_REWRITES_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm
    with Failure _ ->
        GEN_SUB_CONV ONCE_DEPTH_SQCONV ss lev pconvs tm in
  let rec DEPTH_SQCONV (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try let th1 = GEN_SUB_CONV DEPTH_SQCONV ss lev pconvs tm in
        let tm1 = rand(concl th1) in
        let pconvs1 = lookup tm1 net in
        try TRANS th1 (IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs1 tm1)
        with Failure _ -> th1
    with Failure _ ->
        IMP_REWRITES_CONV DEPTH_SQCONV ss lev pconvs tm in
  let rec REDEPTH_SQCONV (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    let th =
      try let th1 = GEN_SUB_CONV REDEPTH_SQCONV ss lev pconvs tm in
          let tm1 = rand(concl th1) in
          let pconvs1 = lookup tm1 net in
          try TRANS th1 (IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs1 tm1)
          with Failure _ -> th1
      with Failure _ ->
          IMP_REWRITES_CONV REDEPTH_SQCONV ss lev pconvs tm in
    try let th' = REDEPTH_SQCONV ss lev (rand(concl th)) in
        TRANS th th'
    with Failure _ -> th in
  let rec TOP_DEPTH_SQCONV (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    let th1 =
      try IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev pconvs tm
      with Failure _ -> GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev pconvs tm in
    try let th2 = TOP_DEPTH_SQCONV ss lev (rand(concl th1)) in
            TRANS th1 th2
    with Failure _ -> th1 in
  let rec TOP_SWEEP_SQCONV (Simpset(net,prover,provers,rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try let th1 = IMP_REWRITES_CONV TOP_SWEEP_SQCONV ss lev pconvs tm in
        try let th2 = TOP_SWEEP_SQCONV ss lev (rand(concl th1)) in
            TRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> GEN_SUB_CONV TOP_SWEEP_SQCONV ss lev pconvs tm in
  ONCE_DEPTH_SQCONV,DEPTH_SQCONV,REDEPTH_SQCONV,
  TOP_DEPTH_SQCONV,TOP_SWEEP_SQCONV;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_DEPTH_SQCONV.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/DEPTH_SQCONV.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REDEPTH_SQCONV.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/TOP_DEPTH_SQCONV.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/TOP_SWEEP_SQCONV.html>

`IMP_REWRITES_CONV strat ss lev` tris to find a conversion for `tm` at level < 4
(i.e., not a congruence rule) which is either unconditional or (if lev > 0) such
that the condition can be rewritten to `T` by `strat ss (lev-1)`.

`RUN_SUB_CONV` is called only by GEN_SUB_CONV; not documented.

`GEN_SUB_CONV strat ss lev` tries to find a congruence rule for `tm`
(i.e. a rule at level 4).  The conclusion of a congruence rule is of the form
`A[x1,...,xn] = A[x1',...,xn']`, so `tm` must be of the form `A[a1,...,an]`.
Each hypothesis of a congruence rule is either of the form
`xi = xi'` or `P[x1',...,x(i-1)'] ==> (xi = xi')`.
In the former case, use `strat ss lev` to rewrite `a1` to `a1'`;
in the latter case, use `AUGMENT_SIMPSET` to add `P[a1',...,a(i-1)']` to `ss`
(getting `ss'`) and use strat ss' lev` for the rewrite.
Combine all of these rewrites to rewrite `A[a1,...,an]` to `A[a1',...,an']`.
If this fails, then if `tm` is `f a` use `strat ss lev` to rewrite `f` to `g`
and `a` to `b` and return `|- f a = g b`.  If `tm` is `\x. a[x]`, then use
`strat ss lev` to rewrite `a[x]` to `b[x]` and return
`|- (\x. a[x]) = (\x. b[x])`.  Throughout `GEN_SUB_CONV` (in both the congruence
rule case, and the combination case), if the call to `strat` fails to rewrite
`a`, then it rewrites `a` to `a`; but if all the calls to `strat` fail (so that
`GEN_SUB_CONV` would rewrite `tm` to `tm`), `GEN_SUB_CONV` fails instead.

Note that there are only two congruence rules used in HOL Light: one for
rewriting `if g then t else e` and one for rewriting `p ==> q`.

`ONCE_DEPTH_SQCONV ss lev` is basically
`(IMP_REWRITES_CONV ONCE_DEPTH_SQCONV ss lev)
  ORELSEC (GEN_SUB_CONV ONCE_DEPTH_SQCONF ss lev)`.

`DEPTH_SQCONV ss lev` is basically
`THENQC (GEN_SUB_CONV DEPTH_SQCONV ss lev)
   (IMP_REWRITES_CONV DEPTH_SQCONV ss lev)`.

`REDEPTH_SQCONV ss lev` is basically `REPEATQC (DEPTH_CONV ss lev)`.

`TOP_DEPTH_SQCONV ss lev` is basically
`REPEATQC ((IMP_REWRITES_CONV TOP_DEPTH_SQCONV ss lev)
            ORELSEC (GEN_SUB_CONV TOP_DEPTH_SQCONV ss lev))`.

`TOP_SWEEP_SQCONV ss lev` is basically
`THENQC (REPEATC (IMP_REWRITES_CONV TOP_SWEEP_SQCONV ss lev))
   (GEN_SUB_CONV TOP_SWEEP_SQCONV ss lev)`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Maintenence of basic rewrites and conv nets for rewriting.                *)
(* ------------------------------------------------------------------------- *)
```
There is a global set of "basic rewrites".  These are canonicalized with
`mk_rewrites false` (so there is no handling of conditional rewrites),
and added to a basic conversion net.

```ocaml
let set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
    set_basic_convs,extend_basic_convs,basic_convs,basic_net =
  let rewrites = ref ([]:thm list)
  and conversions = ref ([]:(string*(term*conv))list)
  and conv_net = ref (empty_net: gconv net) in
  let rehash_convnet() =
    conv_net := itlist (net_of_thm true) (!rewrites)
        (itlist (fun (_,(pat,cnv)) -> net_of_conv pat cnv) (!conversions)
                empty_net) in
  let set_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl; rehash_convnet())
  and extend_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl @ !rewrites; rehash_convnet())
  and basic_rewrites() = !rewrites
  and set_basic_convs cnvs =
    (conversions := cnvs; rehash_convnet())
  and extend_basic_convs (name,patcong) =
    (conversions :=
      (name,patcong)::filter(fun (name',_) -> name <> name') (!conversions);
     rehash_convnet())
  and basic_convs() = !conversions
  and basic_net() = !conv_net in
  set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
  set_basic_convs,extend_basic_convs,basic_convs,basic_net;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/set_basic_rewrites.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/extend_basic_rewrites.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_rewrites.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/set_basic_convs.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/extend_basic_convs.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_convs.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_net.html>

`set_basic_rewrites thl` sets the "basic rewrite" set to `thl`.

`extend_basic_rewrites thl` adds `thl` to the "basic rewrite" set.

`basic_rewrites ()` retrieves the (canonicalised) "basic rewrite" set.

`basic_net ()` retrieves the conversion net for the "basic rewrite" set.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Same thing for the default congruences.                                   *)
(* ------------------------------------------------------------------------- *)
```
There is also a set of basic congruences; since HOL has only two congruence
rules (which are?), I won't bother documenting `set_basic_congs`,
`extend_basic_congs`, `basic_congs`.

```ocaml
let set_basic_congs,extend_basic_congs,basic_congs =
  let congs = ref ([]:thm list) in
  (fun thl -> congs := thl),
  (fun thl -> congs := union' equals_thm thl (!congs)),
  (fun () -> !congs);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/set_basic_congs.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/extend_basic_congs.html>

<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_congs.html>

```ocaml
(* ------------------------------------------------------------------------- *)
(* Main rewriting conversions.                                               *)
(* ------------------------------------------------------------------------- *)

let GENERAL_REWRITE_CONV rep (cnvl:conv->conv) (builtin_net:gconv net) thl =
  let thl_canon = itlist (mk_rewrites false) thl [] in
  let final_net = itlist (net_of_thm rep) thl_canon builtin_net in
  cnvl (REWRITES_CONV final_net);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/GENERAL_REWRITE_CONV.html>

`GENERAL_REWRITE_CONV rep cnvl net thl` canonicalises `thl` with
`mk_rewrites false`, adds these conversions to `net` with `net_of_thm rep`
(giving `final_net`), and then rewrites with `cnvl (REWRITES_CONV final_net)`.

```ocaml
let GEN_REWRITE_CONV (cnvl:conv->conv) thl =
  GENERAL_REWRITE_CONV false cnvl empty_net thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/GEN_REWRITE_CONV.html>

```ocaml
let PURE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true TOP_DEPTH_CONV empty_net thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_REWRITE_CONV.html>

```ocaml
let REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_CONV.html>

```ocaml
let PURE_ONCE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV empty_net thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ONCE_REWRITE_CONV.html>

```ocaml
let ONCE_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV false ONCE_DEPTH_CONV (basic_net()) thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_REWRITE_CONV.html>

```ocaml
(* ------------------------------------------------------------------------- *)
(* Rewriting rules and tactics.                                              *)
(* ------------------------------------------------------------------------- *)

let GEN_REWRITE_RULE cnvl thl = CONV_RULE(GEN_REWRITE_CONV cnvl thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/GEN_REWRITE_RULE.html>

```ocaml
let PURE_REWRITE_RULE thl = CONV_RULE(PURE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_REWRITE_RULE.html>

```ocaml
let REWRITE_RULE thl = CONV_RULE(REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_RULE.html>

```ocaml
let PURE_ONCE_REWRITE_RULE thl = CONV_RULE(PURE_ONCE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ONCE_REWRITE_RULE.html>

```ocaml
let ONCE_REWRITE_RULE thl = CONV_RULE(ONCE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_REWRITE_RULE.html>

```ocaml
let PURE_ASM_REWRITE_RULE thl th =
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ASM_REWRITE_RULE.html>

```ocaml
let ASM_REWRITE_RULE thl th =
    REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASM_REWRITE_RULE.html>

```ocaml
let PURE_ONCE_ASM_REWRITE_RULE thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ONCE_ASM_REWRITE_RULE.html>

```ocaml
let ONCE_ASM_REWRITE_RULE thl th =
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_ASM_REWRITE_RULE.html>

`PURE_ASM_REWRITE_RULE`, `ASM_REWRITE_RULE`,
`PURE_ONCE_ASM_REWRITE_RULE`, `ONCE_ASM_REWRITE_RULE` are the same as the
non-`ASM_` versions, but they add the theorem hypotheses to the rewrite list.

```ocaml
let GEN_REWRITE_TAC cnvl thl = CONV_TAC(GEN_REWRITE_CONV cnvl thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/GEN_REWRITE_TAC.html>

```ocaml
let PURE_REWRITE_TAC thl = CONV_TAC(PURE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_REWRITE_TAC.html>

```ocaml
let REWRITE_TAC thl = CONV_TAC(REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/REWRITE_TAC.html>

```ocaml
let PURE_ONCE_REWRITE_TAC thl = CONV_TAC(PURE_ONCE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ONCE_REWRITE_TAC.html>

```ocaml
let ONCE_REWRITE_TAC thl = CONV_TAC(ONCE_REWRITE_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_REWRITE_TAC.html>

`GEN_REWRITE_TAC`, `PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`,
`ONCE_REWRITE_TAC` are the same as the `_RULE` variants, but use `CONV_TAC`
instead of `CONV_RULE`.

```ocaml
let (PURE_ASM_REWRITE_TAC: thm list -> tactic) =
  ASM PURE_REWRITE_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ASM_REWRITE_TAC.html>

```ocaml
let (ASM_REWRITE_TAC: thm list -> tactic) =
  ASM REWRITE_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASM_REWRITE_TAC.html>

```ocaml
let (PURE_ONCE_ASM_REWRITE_TAC: thm list -> tactic) =
  ASM PURE_ONCE_REWRITE_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ONCE_ASM_REWRITE_TAC.html>

```ocaml
let (ONCE_ASM_REWRITE_TAC: thm list -> tactic) =
  ASM ONCE_REWRITE_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_ASM_REWRITE_TAC.html>

`PURE_ASM_REWRITE_TAC`, `ASM_REWRITE_TAC`, `PURE_ONCE_ASM_REWRITE_TAC`,
`ONCE_ASM_REWRITE_TAC` are the same as the non-`ASM_` variants, but they add
the current assumptions to the rewrite list.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Simplification functions.                                                 *)
(* ------------------------------------------------------------------------- *)

let GEN_SIMPLIFY_CONV (strat:strategy) ss lev thl =
  let ss' = itlist AUGMENT_SIMPSET thl ss in
  TRY_CONV (strat ss' lev);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/GEN_SIMPLIFY_CONV.html>

`GEN_SIMPLIFY_CONV strat ss lev thl` uses `AUGMENT_SIMPSET` to add `thl` to `ss`
(giving `ss'`); then does `TRY_CONV (strat ss' lev)`.

```ocaml
let ONCE_SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV ONCE_DEPTH_SQCONV ss 1;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_SIMPLIFY_CONV.html>

```ocaml
let SIMPLIFY_CONV ss = GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV ss 3;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/SIMPLIFY_CONV.html>

```ocaml
(* ------------------------------------------------------------------------- *)
(* Simple but useful default version.                                        *)
(* ------------------------------------------------------------------------- *)

let empty_ss = Simpset(empty_net,basic_prover,[],mk_rewrites true);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/empty_ss.html>

`empty_ss` is the empty simpset (no conversions in the conversion net).

```ocaml
let basic_ss =
  let rewmaker = mk_rewrites true in
  fun thl ->
    let cthms = itlist rewmaker thl [] in
    let net' = itlist (net_of_thm true) cthms (basic_net()) in
    let net'' = itlist net_of_cong (basic_congs()) net' in
  Simpset(net'',basic_prover,[],rewmaker);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/basic_ss.html>

`basic_ss thl` canonicalises `thl` with `mk_rewrites true`, then adds the
rewrites to `basic_net()` with `net_of_thm true`.  It also adds the basic
congruences and it returns the resulting simpset.

```ocaml
let SIMP_CONV thl = SIMPLIFY_CONV (basic_ss []) thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/SIMP_CONV.html>

```ocaml
let PURE_SIMP_CONV thl = SIMPLIFY_CONV empty_ss thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_SIMP_CONV.html>

```ocaml
let ONCE_SIMP_CONV thl = ONCE_SIMPLIFY_CONV (basic_ss []) thl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_SIMP_CONV.html>

```ocaml
let SIMP_RULE thl = CONV_RULE(SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/SIMP_RULE.html>

```ocaml
let PURE_SIMP_RULE thl = CONV_RULE(PURE_SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_SIMP_RULE.html>

```ocaml
let ONCE_SIMP_RULE thl = CONV_RULE(ONCE_SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_SIMP_RULE.html>

`SIMP_RULE`, `PURE_SIMP_RULE`, `ONCE_SIMP_RULE` are the same as the `_CONV`
variants, but they call `CONV_RULE`.

```ocaml
let SIMP_TAC thl = CONV_TAC(SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/SIMP_TAC.html>

```ocaml
let PURE_SIMP_TAC thl = CONV_TAC(PURE_SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_SIMP_TAC.html>

```ocaml
let ONCE_SIMP_TAC thl = CONV_TAC(ONCE_SIMP_CONV thl);;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_SIMP_TAC.html>

`SIMP_TAC`, `PURE_SIMP_TAC`, `ONCE_SIMP_TAC` are the same as the `_CONV`
variants, but they call `CONV_TAC`.

```ocaml
let ASM_SIMP_TAC = ASM SIMP_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ASM_SIMP_TAC.html>

```ocaml
let PURE_ASM_SIMP_TAC = ASM PURE_SIMP_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/PURE_ASM_SIMP_TAC.html>

```ocaml
let ONCE_ASM_SIMP_TAC = ASM ONCE_SIMP_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ONCE_ASM_SIMP_TAC.html>

`ASM_SIMP_TAC`, `PURE_ASM_SIMP_TAC`, `ONCE_ASM_SIMP_TAC` are the same as the
non-`ASM_` variants, but they add the current assumptions to the rewrite list.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Abbreviation tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let ABBREV_TAC tm =
  let cvs,t = dest_eq tm in
  let v,vs = strip_comb cvs in
  let rs = list_mk_abs(vs,t) in
  let eq = mk_eq(rs,v) in
  let th1 = itlist (fun v th -> CONV_RULE(LAND_CONV BETA_CONV) (AP_THM th v))
                   (rev vs) (ASSUME eq) in
  let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1)) in
  let th3 = PROVE_HYP (EXISTS(mk_exists(v,eq),rs) (REFL rs)) th2 in
  fun (asl,w as gl) ->
    let avoids = itlist (union o frees o concl o snd) asl (frees w) in
    if mem v avoids then failwith "ABBREV_TAC: variable already used" else
    CHOOSE_THEN
     (fun th -> RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE[th]) THEN
                PURE_ONCE_REWRITE_TAC[th] THEN
                ASSUME_TAC th)
     th3 gl;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/ABBREV_TAC.html>

`` ABBREV_TAC `x = a` `` rewrites `a` to `x` in the goal and all assumptions,
then adds `a = x` as a new assumption.

```ocaml
let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;
```
<http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/EXPAND_TAC.html>

`` EXPAND_TAC `x` `` finds the first assumption of the form `t = x`, rewrites
`x` to `t` in the goal, and beta-reduces the goal.

- Previous: [itab.ml](itab.md)
- [Index](index.md)
- Next: [theorems.ml](theorems.md)
