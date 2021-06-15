module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> =
  | Empty
  | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
  match x with
    | Empty -> i1 ()
    | Node (a, (l, r)) -> i2 (a, (l, r))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = (baseBTree id g) x

let rec cataBTree g x = (g << (recBTree (cataBTree g)) << outBTree) x

let rec anaBTree g x = (inBTree << (recBTree (anaBTree g) ) << g) x

let hyloBTree f g x = (cataBTree f << anaBTree g) x

// (3) Map ---------------------------------------------------------------------

let fmap f x = cataBTree (inBTree << baseBTree f id) x

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

// in-order traversal

let inord x =
  let join (a, (l, r)) = l @ a::r
  in either nil join x

let inordt x = cataBTree inord x

// pre-order traversal

let preord x =
  let join (a, (l, r)) = a::l @ r
  in either nil join x

let preordt x = cataBTree preord x

// post-order traversal

let postord x =
  let join (a, (l, r)) = l @ r @ [a]
  in either nil join x

let postordt x = cataBTree postord x

// (4.4) Quicksort -------------------------------------------------------------

let rec part p l =
  match l with
    | [] -> ([], [])
    | (h::t) ->
      let (s, l) = part p t
      in
        if p h then
          (h::s, l)
        else
          (s, h::l)

let qsep l =
  match l with
    | [] -> i1 ()
    | (h :: t) ->
      let (s, l) = part ((>) h) t
      in i2 (h, (s, l))

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let rec delete x y =
  match y with
    | [] -> []
    | (h::t) ->
      if x = h then t
      else h :: delete x t

let union x y = x @ List.fold (flip delete) (List.distinct y) x

let tunion (a, (l, r)) = union (List.map ((@) [a]) l) (List.map ((@) [a]) r)

let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6) Towers of Hanoi -------------------------------------------------------

let present x = inord x

let strategy (d, n) =
  match n with
    | 0 -> i1 ()
    | otherwise -> i2 ((n, d), ((not d, n), (not d, n)))

let hanoi x = hyloBTree present strategy x

// (5) Depth and balancing (using mutual recursion) ----------------------------

let baldepth x =
  let f ((b1, d1), (b2, d2)) = ((b1, b2), (d1, d2))
  let h (a, ((b1, b2), (d1, d2))) =
      (b1 && b2 && abs (d1 - d2) <= 1, 1 + max d1 d2)
  let g x = either (konst (true, 1)) (h << (id >< f)) x
  in cataBTree g x

let balBTree b = (p1 << baldepth) b

let depthBTree b = (p2 << baldepth) b
