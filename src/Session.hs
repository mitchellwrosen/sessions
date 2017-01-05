{-# language TemplateHaskell                    #-}
{-# language UndecidableInstances               #-}
{-# options_ghc -fno-warn-redundant-constraints #-}

module Session
  ( Session(..)
  , Ty(..)
  , Nat(..)
  , Top
  , IsDual
  , AssertDual
  , assertDual
  , sessionReturn
  , sessionLift
  , sessionBind
  , sessionThen
  , send
  , recv
  , offer
  , pickL
  , pickR
  , enter
  , vz
  , vs
  ) where

import GHC.Exts (Constraint)
import GHC.TypeLits (TypeError, ErrorMessage(..))

data Nat
  = Z
  | S Nat

data Ty where
  Send  :: a -> Ty -> Ty
  Recv  :: a -> Ty -> Ty
  Offer :: Ty -> Ty -> Ty
  Pick  :: Ty -> Ty -> Ty
  Rec   :: Ty -> Ty
  Var   :: Nat -> Ty
  Done  :: Ty

class Top a
instance Top a

data Session
       (e  :: [Ty])
       (e' :: [Ty])
       (r  :: Ty)
       (r' :: Ty)
       (c  :: * -> Constraint)
       (m  :: * -> *)
       (a  :: *)
     where
  SSend  :: c a => a -> Session e e ('Send a r) r c m ()
  SRecv  :: c a => Session e e ('Recv a r) r c m a
  SEnter :: Session e (r ': e) ('Rec r) r c m ()
  SZero  :: Session (r ': e) (r ': e) ('Var 'Z) r c m ()
  SSucc  :: Session (r ': e) e ('Var ('S n)) ('Var n) c m ()
  SPickL :: Session e e ('Pick r s) r c m ()
  SPickR :: Session e e ('Pick r s) s c m ()
  SOffer :: Session e e' r t c m a
         -> Session e e' s t c m a
         -> Session e e' ('Offer r s) t c m a

  SPure  :: a -> Session e e r r c m a
  SLift  :: m a -> Session e e r r c m a
  SBind  :: Session e e' r r' c m a
         -> (a -> Session e' e'' r' r'' c m b)
         -> Session e e'' r r'' c m b

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

offer
  :: Session e e' r t c m a
  -> Session e e' s t c m a
  -> Session e e' ('Offer r s) t c m a
offer = SOffer

pickL :: Session e e ('Pick r s) r c m ()
pickL = SPickL

pickR :: Session e e ('Pick r s) s c m ()
pickR = SPickR

enter :: Session e (r ': e) ('Rec r) r c m ()
enter = SEnter

vz :: Session (r ': e) (r ': e) ('Var 'Z) r c m ()
vz = SZero

vs :: Session (r ': e) e ('Var ('S n)) ('Var n) c m ()
vs = SSucc

type family IsDual (r :: Ty) (s :: Ty) :: Constraint where
  IsDual ('Send a r)  ('Recv a s)  = IsDual r s
  IsDual ('Recv a r)  ('Send a s)  = IsDual r s
  IsDual ('Offer r s) ('Pick t u)  = (IsDual r t, IsDual s u)
  IsDual ('Pick r s)  ('Offer t u) = (IsDual r t, IsDual s u)
  IsDual ('Rec r)     ('Rec s)     = IsDual r s
  IsDual ('Var n)     ('Var n)     = ()
  IsDual 'Done        'Done        = ()
  IsDual a            b            = TypeError ('Text "Not dual:"
                                                ':$$:
                                                'ShowType a
                                                ':$$:
                                                'ShowType b)


data AssertDual (s1 :: Ty) (s2 :: Ty) = AssertDual

assertDual :: IsDual s1 s2 => AssertDual s1 s2
assertDual = $([| AssertDual |])
