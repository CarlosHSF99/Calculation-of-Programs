
// (c) MP-I (1998/9-2006/7) and CP (2005/6-2016/7)

module BTree

open Cp
//import Data.Monoid
//import Control.Applicative

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)
//type LTree<'a> = Leaf of 'a | Fork of LTree<'a> * LTree<'a>

let inBTree x = either (konst Empty x) Node x // PROBABLY DOESN'T WORK

let outBTree x =
     match x with
     | Empty -> i1 ()
     | Node (a,(t1,t2)) -> i2 (a,(t1,t2))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree f = baseBTree id f          // that is:  id -|- (id >< (f >< f))

let rec cataBTree g = g << (recBTree (cataBTree g)) << outBTree

let rec anaBTree g = inLBree << (recBTree (anaBTree g) ) << g

let hyloBTree a c = cataBTree a << anaBTree c

// (3) Map ---------------------------------------------------------------------

//instance Functor BTree
//         where fmap f = cataBTree ( inBTree . baseBTree f id )
let fmap f = cataBTree ( inLBree << baseLBree f id )

// equivalent to:
// let fmap f = anaBTree ( baseBTree f id << outBTree )
