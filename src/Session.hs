{-# language TemplateHaskell                    #-}
{-# language UndecidableInstances               #-}
{-# options_ghc -fno-warn-redundant-constraints #-}

module Session
  ( -- * Session types
    Session(..)
  , Ty(..)
  , Nat(..)
  , SessionList(..)
  , sessionListIx
  , Elem(..)
  , elemToInt
  , unsafeIntToElem
  , Top
  , AssertDual
  , assertDual
    -- * Rebindable syntax combinators
  , sessionReturn
  , sessionLift
  , sessionBind
  , sessionThen
    -- * Session combinators
  , send
  , recv
  , offer
  , offer3
  , offer4
  , offer5
  , offer6
  , offer7
  , offer8
  , offer9
  , offer10
  , pick0
  , pick1
  , pick2
  , pick3
  , pick4
  , pick5
  , pick6
  , pick7
  , pick8
  , pick9
  , label
  , goto
  ) where

import GHC.Exts (Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Unsafe.Coerce (unsafeCoerce)

data Nat
  = Z
  | S Nat

data Ty where
  Send  :: a -> Ty -> Ty
  Recv  :: a -> Ty -> Ty
  Offer :: [Ty] -> Ty
  Pick  :: [Ty] -> Ty
  Label :: a -> Ty -> Ty
  Goto  :: a -> Ty
  Done  :: Ty

class Top a
instance Top a

data Session
       (e  :: [(l, Ty)])
       (e' :: [(l, Ty)])
       (r  :: Ty)
       (r' :: Ty)
       (c  :: * -> Constraint)
       (m  :: * -> *)
       (a  :: *)
     where
  SSend  :: c a => a -> Session e e ('Send a r) r c m ()
  SRecv  :: c a => Session e e ('Recv a r) r c m a
  SPick  :: Elem r rs -> Session e e ('Pick rs) r c m ()
  SOffer :: SessionList e e' s c m a rs -> Session e e' ('Offer rs) s c m a
  SLabel :: Session e ('(l, r) ': e) ('Label l r) r c m ()
  SGoto  :: Labeled e e' l r => Session e e' ('Goto l) r c m ()

  SPure  :: a -> Session e e r r c m a
  SLift  :: m a -> Session e e r r c m a
  SBind  :: Session e e' r r' c m a
         -> (a -> Session e' e'' r' r'' c m b)
         -> Session e e'' r r'' c m b

class Labeled e e' l r | l r e -> e', l e -> r where
instance {-# OVERLAPPING #-} Labeled ('(l, r) ': e) ('(l, r) ': e) l r
instance Labeled e e' l r => Labeled (x ': e) e' l r

data SessionList
       (e :: [(l, Ty)])
       (e' :: [(l, Ty)])
       (s  :: Ty)
       (c  :: * -> Constraint)
       (m  :: * -> *)
       (a  :: *)
       (rs :: [Ty])
     where
  SessionListLast :: Session e e' r s c m a -> SessionList e e' s c m a '[r]
  SessionListCons :: Session e e' r s c m a
                  -> SessionList e e' s c m a rs
                  -> SessionList e e' s c m a (r ': rs)

data Elem (x :: k) (xs :: [k]) where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

unsafeIntToElem :: Int -> Elem x xs
unsafeIntToElem n | n < 0 = error ("unsafeIntToElem: " ++ show n)
unsafeIntToElem 0 = unsafeCoerce Here
unsafeIntToElem n = unsafeCoerce (There (unsafeIntToElem (n-1)))

elemToInt :: Elem x xs -> Int
elemToInt Here = 0
elemToInt (There e) = elemToInt e + 1

sessionListIx
  :: Elem r rs -> SessionList e e' s c m a rs -> Session e e' r s c m a
sessionListIx Here (SessionListLast s) = s
sessionListIx Here (SessionListCons s _) = s
sessionListIx (There _) (SessionListLast _) = error "impossible"
sessionListIx (There e) (SessionListCons _  ss) = sessionListIx e ss

sessionReturn :: a -> Session e e r r c m a
sessionReturn = SPure

sessionLift :: m a -> Session e e r r c m a
sessionLift = SLift

sessionBind
  :: Session e e' r r' c m a
  -> (a -> Session e' e'' r' r'' c m b)
  -> Session e e'' r r'' c m b
sessionBind = SBind

sessionThen
  :: Session e e' r r' c m a
  -> Session e' e'' r' r'' c m b
  -> Session e e'' r r'' c m b
sessionThen s1 s2 = SBind s1 (\_ -> s2)

send :: c a => a -> Session e e ('Send a r) r c m ()
send = SSend

recv :: c a => Session e e ('Recv a r) r c m a
recv = SRecv

offer_
  :: SessionList e e' s c m a rs
  -> Session e e' ('Offer rs) s c m a
offer_ = SOffer

offer
  :: Session e e' r t c m a
  -> Session e e' s t c m a
  -> Session e e' ('Offer '[r, s]) t c m a
offer s1 s2 = offer_ (SessionListCons s1 (SessionListLast s2))

offer3
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' ('Offer '[p, q, r]) z c m a
offer3 s1 s2 s3 =
  offer_ (SessionListCons s1 (SessionListCons s2 (SessionListLast s3)))

offer4
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' ('Offer '[p, q, r, s]) z c m a
offer4 s1 s2 s3 s4 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListLast s4))))

offer5
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' ('Offer '[p, q, r, s, t]) z c m a
offer5 s1 s2 s3 s4 s5 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListLast s5)))))

offer6
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' u z c m a
  -> Session e e' ('Offer '[p, q, r, s, t, u]) z c m a
offer6 s1 s2 s3 s4 s5 s6 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListCons s5 (SessionListLast s6))))))

offer7
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' u z c m a
  -> Session e e' v z c m a
  -> Session e e' ('Offer '[p, q, r, s, t, u, v]) z c m a
offer7 s1 s2 s3 s4 s5 s6 s7 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListCons s5 (SessionListCons s6
      (SessionListLast s7)))))))

offer8
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' u z c m a
  -> Session e e' v z c m a
  -> Session e e' w z c m a
  -> Session e e' ('Offer '[p, q, r, s, t, u, v, w]) z c m a
offer8 s1 s2 s3 s4 s5 s6 s7 s8 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListCons s5 (SessionListCons s6
      (SessionListCons s7 (SessionListLast s8))))))))

offer9
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' u z c m a
  -> Session e e' v z c m a
  -> Session e e' w z c m a
  -> Session e e' x z c m a
  -> Session e e' ('Offer '[p, q, r, s, t, u, v, w, x]) z c m a
offer9 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListCons s5 (SessionListCons s6
      (SessionListCons s7 (SessionListCons s8 (SessionListLast s9)))))))))

offer10
  :: Session e e' p z c m a
  -> Session e e' q z c m a
  -> Session e e' r z c m a
  -> Session e e' s z c m a
  -> Session e e' t z c m a
  -> Session e e' u z c m a
  -> Session e e' v z c m a
  -> Session e e' w z c m a
  -> Session e e' x z c m a
  -> Session e e' y z c m a
  -> Session e e' ('Offer '[p, q, r, s, t, u, v, w, x, y]) z c m a
offer10 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 =
  offer_
    (SessionListCons s1 (SessionListCons s2 (SessionListCons s3
      (SessionListCons s4 (SessionListCons s5 (SessionListCons s6
      (SessionListCons s7 (SessionListCons s8 (SessionListCons s9
      (SessionListLast s10))))))))))

pick_ :: Elem r rs -> Session e e ('Pick rs) r c m ()
pick_ = SPick

pick0 :: Session e e ('Pick (z ': zs)) z c m ()
pick0 = pick_ Here

pick1 :: Session e e ('Pick (y ': z ': zs)) z c m ()
pick1 = pick_ (There Here)

pick2 :: Session e e ('Pick (x ': y ': z ': zs)) z c m ()
pick2 = pick_ (There (There Here))

pick3 :: Session e e ('Pick (w ': x ': y ': z ': zs)) z c m ()
pick3 = pick_ (There (There (There Here)))

pick4 :: Session e e ('Pick (v ': w ': x ': y ': z ': zs)) z c m ()
pick4 = pick_ (There (There (There (There Here))))

pick5 :: Session e e ('Pick (u ': v ': w ': x ': y ': z ': zs)) z c m ()
pick5 = pick_ (There (There (There (There (There Here)))))

pick6 :: Session e e ('Pick (t ': u ': v ': w ': x ': y ': z ': zs)) z c m ()
pick6 = pick_ (There (There (There (There (There (There Here))))))

pick7 :: Session e e ('Pick (s ': t ': u ': v ': w ': x ': y ': z ': zs)) z c m ()
pick7 = pick_ (There (There (There (There (There (There (There Here)))))))

pick8 :: Session e e ('Pick (r ': s ': t ': u ': v ': w ': x ': y ': z ': zs)) z c m ()
pick8 = pick_ (There (There (There (There (There (There (There (There Here))))))))

pick9 :: Session e e ('Pick (q ': r ': s ': t ': u ': v ': w ': x ': y ': z ': zs)) z c m ()
pick9 = pick_ (There (There (There (There (There (There (There (There (There Here)))))))))

label :: a -> Session e ('(l, r) ': e) ('Label l r) r c m ()
label _ = SLabel

goto :: Labeled e e' l r => a -> Session e e' ('Goto l) r c m ()
goto _ = SGoto

type family IsDual (r :: Ty) (s :: Ty) :: Constraint where
  IsDual ('Send a r)  ('Recv a s)    = IsDual r s
  IsDual ('Recv a r)  ('Send a s)    = IsDual r s
  IsDual ('Offer rs)  ('Pick ss)     = MapIsDual rs ss
  IsDual ('Pick rs)   ('Offer ss)    = MapIsDual rs ss
  IsDual ('Label l r) ('Label l s) = IsDual r s
  IsDual ('Goto l)    ('Goto l)      = ()
  IsDual 'Done        'Done          = ()
  IsDual r            s              = NotDual r s

type family MapIsDual (rs :: [Ty]) (ss :: [Ty]) :: Constraint where
  MapIsDual rs ss = MapIsDual' rs ss rs ss

type family MapIsDual' (rs0 :: [Ty]) (ss0 :: [Ty]) (rs :: [Ty]) (ss :: [Ty]) :: Constraint where
  MapIsDual' rs0 ss0 '[] '[] = ()
  MapIsDual' rs0 ss0 (r ': rs) (s ': ss) = (IsDual r s, MapIsDual' rs0 ss0 rs ss)
  MapIsDual' rs0 ss0 rs ss = NotDual rs0 ss0

type family NotDual r s :: Constraint where
  NotDual r s = TypeError ('Text "Not dual:"
                           ':$$:
                           'ShowType r
                           ':$$:
                           'ShowType s)

data AssertDual (s1 :: Ty) (s2 :: Ty) = AssertDual

assertDual :: IsDual s1 s2 => AssertDual s1 s2
assertDual = $([| AssertDual |])
