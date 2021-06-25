// (c) MP-I (1998/9-2006/7) and CP (2005/6-2016/7)

module cp2021t

open Cp
//import Data.List
//import Data.Monoid

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)


let inBTree x = (either (konst Empty) Node) x

let outBTree x =
    match x with
    | Empty  -> i1 ()
    | Node (a,(b1,b2)) -> i2 (a,(b1,b2))

// (2) Ana + cata + hylo -------------------------------------------------------

// recBTree g = id -|- (id >< (g >< g))

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g = g << (recBTree (cataBTree g)) << outBTree 

let rec anaBTree g = inBTree << (recBTree (anaBTree g) ) << g

let hyloBTree h g = cataBTree h << anaBTree g

// (3) Map ---------------------------------------------------------------------

//instance Functor BTree
//         where fmap f = cataBTree ( inBTree . baseBTree f id )
let fmap f = cataBTree ( inBTree << baseBTree f id )

// equivalent to:
//       where fmap f = anaBTree ( baseBTree f id . outBTree )


// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let insord x = 
        let join(x,(l,r))=l @ [x] @ r
        in either nil join x

let inordt x = cataBTree insord  x                 // in-order traversal


let preord x =
        let  f(x,(l,r)) = x :: l @ r
        in (either nil f) x

let preordt x = cataBTree preord x // pre-order traversal

let postordt x = 
        let f(x,(l,r)) = l @ r @ [x]
        in cataBTree (either nil f) x

// (4.4) Quicksort -------------------------------------------------------------

let menor x z = z < x

let rec part p x =
    match x with
    | [] -> ([],[])
    | (h::t) -> if p h then let (s,l) = part p t in (h::s,l) else let (s,l) = part p t in (s,h::l)


let qsep x =
    match x with
    | [] -> Left ()
    | (h::t) -> Right (h,(part (menor h) t))

let qSort  x = hyloBTree insord qsep x // the same as (cataBTree inord) . (anaBTree qsep)



(* pointwise versions:
qSort [] = []
qSort (h:t) = let (t1,t2) = part (<h) t
              in  qSort t1 ++ [h] ++ qSort t2

or, using list comprehensions:

qSort [] = []
qSort (h:t) = qSort [ a | a <- t , a < h ] ++ [h] ++ 
              qSort [ a | a <- t , a >= h ]

*)

// (4.5) Traces ----------------------------------------------------------------

let cons x z = x::z

let rec elem x l =
    match l with
    | [] -> false
    | (h::t) -> if x=h then true else elem x t

let rec union l ls =
    match ls with
    | [] -> l
    | (h::t) -> if elem h l then union l t else (union l t) @ [h]

let tunion (a,(l,r)) = union (List.map (cons a) l) (List.map (cons a) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x


// (4.6) Towers of Hanoi -------------------------------------------------------

// pointwise:
// hanoi(d,0) = []
// hanoi(d,n+1) = (hanoi (not d,n)) ++ [(n,d)] ++ (hanoi (not d, n))

let present x = insord x // same as in qSort

let strategy (d,n) =
        match (d,n) with
        | (d,0) -> i1 ()
        | (d,n) -> i2 ((n-1,d),((not d,n-1),(not d,n-1))) 

let hanoi x = hyloBTree present strategy x

(*
    The Towers of Hanoi problem comes from a puzzle marketed in 1883
    by the French mathematician Édouard Lucas, under the pseudonym
    Claus. The puzzle is based on a legend according to which
    there is a temple, apparently in Bramah rather than in Hanoi as
    one might expect, where there are three giant poles fixed in the
    ground. On the first of these poles, at the time of the world's
    creation, God placed sixty four golden disks, each of different
    size, in decreasing order of size. The Bramin monks were given
    the task of moving the disks, one per day, from one pole to another
    subject to the rule that no disk may ever be above a smaller disk.
    The monks' task would be complete when they had succeeded in moving
    all the disks from the first of the poles to the second and, on
    the day that they completed their task the world would come to
    an end!
    
    There is a well­known inductive solution to the problem given
    by the pseudocode below. In this solution we make use of the fact
    that the given problem is symmetrical with respect to all three
    poles. Thus it is undesirable to name the individual poles. Instead
    we visualize the poles as being arranged in a circle; the problem
    is to move the tower of disks from one pole to the next pole in
    a specified direction around the circle. The code defines H n d
    to be a sequence of pairs (k,d') where n is the number of disks,
    k is a disk number and d and d' are directions. Disks are numbered
    from 0 onwards, disk 0 being the smallest. (Assigning number 0
    to the smallest rather than the largest disk has the advantage
    that the number of the disk that is moved on any day is independent
    of the total number of disks to be moved.) Directions are boolean
    values, true representing a clockwise movement and false an anti­clockwise
    movement. The pair (k,d') means move the disk numbered k from
    its current position in the direction d'. The semicolon operator
    concatenates sequences together, [] denotes an empty sequence
    and [x] is a sequence with exactly one element x. Taking the pairs
    in order from left to right, the complete sequence H n d prescribes
    how to move the n smallest disks one­by­one from one pole to the
    next pole in the direction d following the rule of never placing
    a larger disk on top of a smaller disk.
    
    H 0     d = [],
    H (n+1) d = H n ¬d ; [ (n, d) ] ; H n ¬d.
    
    (excerpt from R. Backhouse, M. Fokkinga / Information Processing
    Letters 77 (2001) 71--76)
   
   *)
// (5) Depth and balancing (using mutual recursion) --------------------------

let h (a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)

let f ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))

let baldepth x = 
    let g = either (konst(true,1)) (h << (id><f))
    in cataBTree g x


let balBTree x = p1 (baldepth x)

let depthBTree x = p2 (baldepth x)


(*
-- (6) Going polytipic -------------------------------------------------------

-- natural transformation from base functor to monoid
tnat :: Monoid c => (a -> c) -> Either () (a,(c, c)) -> c
tnat f = either (const mempty) (theta . (f >< theta))
         where theta = uncurry mappend

-- monoid reduction 

monBTree f = cataBTree (tnat f)

-- alternative to (4.2) serialization ----------------------------------------

preordt' = monBTree singl

-- alternative to (4.1) counting ---------------------------------------------

countBTree' = monBTree (const (Sum 1))

-- (7) Zipper ----------------------------------------------------------------

data Deriv a = Dr Bool a (BTree a)

type Zipper a = [ Deriv a ]

plug :: Zipper a -> BTree a -> BTree a
plug [] t = t
plug ((Dr False a l):z) t = Node (a,(plug z t,l))
plug ((Dr True  a r):z) t = Node (a,(r,plug z t))

---------------------------- end of library ----------------------------------
*)
