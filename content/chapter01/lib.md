---
title: lib.ml
---

[Original file](https://github.com/jrh13/hol-light/blob/master/lib.ml)

This is where the actual OCaml gets started.

```ocaml
let fail() = failwith "";;
```
Saves us a few vital characters.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let curry f x y = f(x,y);;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/curry.html

```ocaml
let uncurry f(x,y) = f x y;;

let I x = x;;

let K x y = x;;

let C f x y = f y x;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/C.html

```ocaml
let W f x = f x x;;
```
This appears to be a variant of the
[B, C, K, W system](https://en.wikipedia.org/wiki/B,_C,_K,_W_system).
I'll try and keep an eye out for where they're used later and put some links
here.

```ocaml
let (o) = fun f g x -> f(g x);;

let (F_F) = fun f g (x,y) -> (f x,g y);;
```
Composition and 'apply over pairs' (I wonder if this has a name?
I've seen it mentioned in a paper from Mark Adams comparing HOL systems).

```ocaml
(* ------------------------------------------------------------------------- *)
(* List basics.                                                              *)
(* ------------------------------------------------------------------------- *)

let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rec last l =
  match l with
    [x] -> x
  | (h::t) -> last t
  | [] -> failwith "last";;

let rec butlast l =
  match l with
    [_] -> []
  | (h::t) -> h::(butlast t)
  | [] -> failwith "butlast";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/butlast.html

```ocaml
let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;

let rev =
  let rec rev_append acc l =
    match l with
      [] -> acc
    | h::t -> rev_append (h::acc) t in
  fun l -> rev_append [] l;;

let rec map2 f l1 l2 =
  match (l1,l2) with
    [],[] -> []
  | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
  | _ -> failwith "map2: length mismatch";;
```
These are pretty standard functional goodies.  I'm not really sure why they are
preferable to the standard library versions.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Attempting function or predicate applications.                            *)
(* ------------------------------------------------------------------------- *)

let can f x = try (f x; true) with Failure _ -> false;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/can.html

```ocaml
let check p x = if p x then x else failwith "check";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/check.html

These are quite neat.  I wonder if I can think of anything to say about them.
`can` makes it very easy to define `is_` functions?

Are these definitions shadowed in `metis.ml`?

```ocaml
(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let rec repeat f x =
  try let y = f x in repeat f y with Failure _ -> x;;
```
Pretty standard again.

```ocaml
(* ------------------------------------------------------------------------- *)
(* To avoid consing in various situations, we propagate this exception.      *)
(* I should probably eliminate this and use pointer EQ tests instead.        *)
(* ------------------------------------------------------------------------- *)

exception Unchanged;;
```
This does seem a little hacky.  I wonder if it still results in a measurable
performance improvement.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Various versions of list iteration.                                       *)
(* ------------------------------------------------------------------------- *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec rev_itlist f l b =
  match l with
    [] -> b
  | (h::t) -> rev_itlist f t (f h b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

let rec rev_itlist2 f l1 l2 b =
   match (l1,l2) with
     ([],[]) -> b
   | (h1::t1,h2::t2) -> rev_itlist2 f t1 t2 (f h1 h2 b)
      | _ -> failwith "rev_itlist2";;
```
A whole bouquet.  It strikes me as odd that `end_itlist` doesn't apply `f` to
the final `x`.  Let's look up some uses of it.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

let rec splitlist dest x =
  try let l,r = dest x in
      let ls,res = splitlist dest r in
      (l::ls,res)
  with Failure _ -> ([],x);;

let rev_splitlist dest =
  let rec rsplist ls x =
    try let l,r = dest x in
        rsplist (r::ls) l
    with Failure _ -> (x,ls) in
  fun x -> rsplist [] x;;

let striplist dest =
  let rec strip x acc =
    try let l,r = dest x in
        strip l (strip r acc)
    with Failure _ -> x::acc in
  fun x -> strip x [];;
```
Again, I should look up some examples from other parts of the code.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Apply a destructor as many times as elements in list.                     *)
(* ------------------------------------------------------------------------- *)

let rec nsplit dest clist x =
  if clist = [] then [],x else
  let l,r = dest x in
  let ll,y = nsplit dest (tl clist) r in
  l::ll,y;;
```
For this one too...

```ocaml
(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

let rec replicate x n =
    if n < 1 then []
    else x::(replicate x (n - 1));;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;
```
I don't think these require much comment.  `m -- n` generates the sequence m to
n inclusive.

http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/.upto.html

```ocaml
(* ------------------------------------------------------------------------- *)
(* Various useful list operations.                                           *)
(* ------------------------------------------------------------------------- *)

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) && forall p t;;

let rec forall2 p l1 l2 =
  match (l1,l2) with
    [],[] -> true
  | (h1::t1,h2::t2) -> p h1 h2 && forall2 p t1 t2
  | _ -> false;;

let rec exists p l =
  match l with
    [] -> false
  | h::t -> p(h) || exists p t;;

let length =
  let rec len k l =
    if l = [] then k else len (k + 1) (tl l) in
  fun l -> len 0 l;;

let rec filter p l =
  match l with
    [] -> l
  | h::t -> let t' = filter p t in
            if p(h) then if t'==t then l else h::t'
            else t';;

let rec partition p l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = partition p t in
            if p(h) then (if yes == t then l,[] else h::yes,no)
            else (if no == t then [],l else yes,h::no);;

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest;;

let rec find p l =
  match l with
      [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let flat l = itlist (@) l [];;

let rec remove p l =
  match l with
    [] -> failwith "remove"
  | (h::t) -> if p(h) then h,t else
              let y,n = remove p t in y,h::n;;

let rec chop_list n l =
  if n = 0 then [],l else
  try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
  with Failure _ -> failwith "chop_list";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/chop_list.html

```ocaml
let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
  ind 0;;
```
Again, a few of these exist in the standard library.  I wonder if these are
from a time before they were included, or if John's just a control freak!

```ocaml
(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 || mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

let intersect l1 l2 = filter (fun x -> mem x l2) l1;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

let subset l1 l2 = forall (fun t -> mem t l2) l1;;

let set_eq l1 l2 = subset l1 l2 && subset l2 l1;;
```
These don't seem too troublesome.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare x a = 0 then y else assoc a t
  | [] -> failwith "find";;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/assoc.html

```ocaml
let rec rev_assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assoc a t
  | [] -> failwith "find";;
```
Nice and simple.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Zipping, unzipping etc.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec unzip =
  function [] -> [],[]
         | ((a,b)::rest) -> let alist,blist = unzip rest in
                            (a::alist,b::blist);;
```
Dum dee dum.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Sharing out a list according to pattern in list-of-lists.                 *)
(* ------------------------------------------------------------------------- *)

let rec shareout pat all =
  if pat = [] then [] else
  let l,r = chop_list (length (hd pat)) all in
  l::(shareout (tl pat) r);;
```
This definitely deserves some examples!!

```ocaml
(* ------------------------------------------------------------------------- *)
(* Iterating functions over lists.                                           *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;
```
Very imperative.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Sorting.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;
```
There's also `mergesort` below.  Do they behave identically?

```ocaml
(* ------------------------------------------------------------------------- *)
(* Removing adjacent (NB!) equal elements from list.                         *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if Pervasives.compare x y = 0 then t' else
                      if t'==t then l else x::t'
 | _ -> l;;
```
I'm sure I learnt this as `destutter`.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Convert list into set by eliminating duplicates.                          *)
(* ------------------------------------------------------------------------- *)

let setify s = uniq (sort (fun x y -> Pervasives.compare x y <= 0) s);;
```
Why isn't this with the set functions above?!

```ocaml
(* ------------------------------------------------------------------------- *)
(* String operations (surely there is a better way...)                       *)
(* ------------------------------------------------------------------------- *)

let implode l = itlist (^) l "";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;
```
Maybe something from `Str`?

```ocaml
(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let gcd =
  let rec gxd x y =
    if y = 0 then x else gxd y (x mod y) in
  fun x y -> let x' = abs x and y' = abs y in
              if x' < y' then gxd y' x' else gxd x' y';;
```
Nothing to see here.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Some useful functions on "num" type.                                      *)
(* ------------------------------------------------------------------------- *)

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10;;

let pow2 n = power_num num_2 (Int n);;
let pow10 n = power_num num_10 (Int n);;

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r');;

let numerator = fst o numdom
and denominator = snd o numdom;;

let gcd_num n1 n2 =
  num_of_big_int(Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2));;

let lcm_num x y =
  if x =/ num_0 && y =/ num_0 then num_0
  else abs_num((x */ y) // gcd_num x y);;
```
Not many surprises here.

```ocaml
(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/allpairs.html

Example!

```ocaml
(* ------------------------------------------------------------------------- *)
(* Issue a report with a newline.                                            *)
(* ------------------------------------------------------------------------- *)

let report s =
  Format.print_string s; Format.print_newline();;

(* ------------------------------------------------------------------------- *)
(* Convenient function for issuing a warning.                                *)
(* ------------------------------------------------------------------------- *)

let warn cond s =
  if cond then report ("Warning: "^s) else ();;

(* ------------------------------------------------------------------------- *)
(* Flags to switch on verbose mode.                                          *)
(* ------------------------------------------------------------------------- *)

let verbose = ref true;;
let report_timing = ref true;;

(* ------------------------------------------------------------------------- *)
(* Switchable version of "report".                                           *)
(* ------------------------------------------------------------------------- *)

let remark s =
  if !verbose then report s else ();;
```
I don't think there's much of interest here.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Time a function.                                                          *)
(* ------------------------------------------------------------------------- *)

let time f x =
  if not (!report_timing) then f x else
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time)));
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string("Failed after (user) CPU time of "^
                          (string_of_float(finish_time -. start_time))^": ");
      raise e;;
```
Timing could be fun.  Where is it used?

```ocaml
(* ------------------------------------------------------------------------- *)
(* Versions of assoc and rev_assoc with default rather than failure.         *)
(* ------------------------------------------------------------------------- *)

let rec assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare x a = 0 then y else assocd a t d;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/assocd.html

```ocaml
let rec rev_assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assocd a t d;;
```
I'd put these with the other versions above too.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Version of map that avoids rebuilding unchanged subterms.                 *)
(* ------------------------------------------------------------------------- *)

let rec qmap f l =
  match l with
    h::t -> let h' = f h and t' = qmap f t in
            if h' == h && t' == t then l else h'::t'
  | _ -> l;;
```
This looks potentially interesting.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Merging and bottom-up mergesort.                                          *)
(* ------------------------------------------------------------------------- *)

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

let mergesort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;
```
Again, is this better than `sort` above?  Why have both?  Are either of them
better than the generic sort in the standard library?  Is there a generic
sort in the standard library?!

```ocaml
(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

let increasing f x y = Pervasives.compare (f x) (f y) < 0;;

let decreasing f x y = Pervasives.compare (f x) (f y) > 0;;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;
```
Source for Patricia trees.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analagous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;
```
Looks okay.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

let ran f = setify(foldl (fun a x y -> y::a) [] f);;
```
Example!

```ocaml
(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> let c = Pervasives.compare x a in
                  if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
                -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/applyd.html

```ocaml
let apply f = applyd f (fun x -> failwith "apply");;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/apply.html

```ocaml
let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;
```
There are definitely things to say here.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then t
          else if c < 0 then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else (match l' with Empty -> r | _ -> Branch(p,b,l',r))
          else
            let r' = und r in
            if r' == r then t
            else (match r' with Empty -> l | _ -> Branch(p,b,l,r'))
      | _ -> t in
    und;;
```
And here.  What is this??

```ocaml
(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

let (|->),combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then xy::t
          else if c < 0 then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          let c = Pervasives.compare x1 x2 in
          if c < 0 then xy1::(combine_list op z t1 l2)
          else if c > 0 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z lf l with
                 Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z lf r with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch k lf p br
    | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z l lf with
                Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z r lf with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch p br k lf
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              (match combine op z l1 t2 with
                 Empty -> r1 | l -> Branch(p1,b1,l,r1))
            else
              (match combine op z r1 t2 with
                 Empty -> l1 | r -> Branch(p1,b1,l1,r))
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              (match combine op z t1 l2 with
                 Empty -> r2 | l -> Branch(p2,b2,l,r2))
            else
              (match combine op z t1 r2 with
                 Empty -> l2 | r -> Branch(p2,b2,l2,r))
          else if p1 = p2 then
           (match (combine op z l1 l2,combine op z r1 r2) with
              (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/.valmod.html

http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/combine.html

Bloop.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let (|=>) = fun x y -> (x |-> y) undefined;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/.singlefun.html

```ocaml
(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> hd l
  | Branch(b,p,t1,t2) -> choose t1;;
```
http://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/choose.html

Hmm

```ocaml
(* ------------------------------------------------------------------------- *)
(* Install a trivial printer for the general polymorphic case.               *)
(* ------------------------------------------------------------------------- *)

let print_fpf (f:('a,'b)func) = Format.print_string "<func>";;

#install_printer print_fpf;;
```
Double hmm

```ocaml
(* ------------------------------------------------------------------------- *)
(* Set operations parametrized by equality (from Steven Obua).               *)
(* ------------------------------------------------------------------------- *)

let rec mem' eq =
  let rec mem x lis =
    match lis with
      [] -> false
    | (h::t) -> eq x h || mem x t
  in mem;;

let insert' eq x l =
  if mem' eq x l then l else x::l;;

let union' eq l1 l2 = itlist (insert' eq) l1 l2;;

let unions' eq l = itlist (union' eq) l [];;

let subtract' eq l1 l2 = filter (fun x -> not (mem' eq x l2)) l1;;
```
These should be with the others in a *Sets* section!  But not much to comment
on.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Accepts decimal, hex or binary numeral, using C notation 0x... for hex    *)
(* and analogous 0b... for binary.                                           *)
(* ------------------------------------------------------------------------- *)

let num_of_string =
  let values =
   ["0",0; "1",1; "2",2; "3",3; "4",4;
    "5",5; "6",6; "7",7; "8",8; "9",9;
    "a",10; "A",10; "b",11; "B",11;
    "c",12; "C",12; "d",13; "D",13;
    "e",14; "E",14; "f",15; "F",15] in
  let valof b s =
    let v = Int(assoc s values) in
    if v </ b then v else failwith "num_of_string: invalid digit for base"
  and two = num_2 and ten = num_10 and sixteen = Int 16 in
  let rec num_of_stringlist b l =
    match l with
      [] -> failwith "num_of_string: no digits after base indicator"
    | [h] -> valof b h
    | h::t -> valof b h +/ b */ num_of_stringlist b t in
  fun s ->
    match explode(s) with
        [] -> failwith "num_of_string: no digits"
      | "0"::"x"::hexdigits -> num_of_stringlist sixteen (rev hexdigits)
      | "0"::"b"::bindigits -> num_of_stringlist two (rev bindigits)
      | decdigits -> num_of_stringlist ten (rev decdigits);;
```
I don't think there's much of interest here.

```ocaml
(* ------------------------------------------------------------------------- *)
(* Convenient conversion between files and (lists of) strings.               *)
(* ------------------------------------------------------------------------- *)

let strings_of_file filename =
  let fd = try Pervasives.open_in filename
           with Sys_error _ ->
             failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    try let l = Pervasives.input_line fd in
        suck_lines (l::acc)
    with End_of_file -> rev acc in
  let data = suck_lines [] in
  (Pervasives.close_in fd; data);;

let string_of_file filename =
  end_itlist (fun s t -> s^"\n"^t) (strings_of_file filename);;

let file_of_string filename s =
  let fd = Pervasives.open_out filename in
  output_string fd s; close_out fd;;
```
These file interactions always drive me crazy in OCaml.

- Previous: [system.ml](system.md)
- [Index](index.md)
- Next: [fusion.ml](fusion.md)
