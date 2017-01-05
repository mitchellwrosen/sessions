{-# language PartialTypeSignatures                #-}
{-# language RebindableSyntax                     #-}
{-# options_ghc -fno-warn-partial-type-signatures #-}

module PrintSession where

import Session

import Data.Serialize (Serialize)
import Data.String
import Prelude hiding ((>>=), (>>), return)

--------------------------------------------------------------------------------
-- Rebound syntax

return :: a -> Session e e r r c m a
return = sessionReturn

lift :: m a -> Session e e r r c m a
lift = sessionLift

(>>=)
  :: Session e e' r r' c m a
  -> (a -> Session e' e'' r' r'' c m b)
  -> Session e e'' r r'' c m b
(>>=) = sessionBind

(>>)
  :: Session e e' r r' c m a
  -> Session e' e'' r' r'' c m b
  -> Session e e'' r r'' c m b
(>>) = sessionThen


--------------------------------------------------------------------------------
-- Print server

type ServerProtocol = 'Offer 'Done ('Recv String ('Var 'Z))

server :: Session '[] _ ('Rec ServerProtocol) 'Done Serialize IO ()
server = do
  enter
  loop
 where
  loop :: Session '[ServerProtocol] _ ServerProtocol 'Done Serialize IO ()
  loop =
    offer
      (return ())
      (do
        s <- recv
        lift (putStrLn s)
        vz
        loop)


--------------------------------------------------------------------------------
-- Print client

type ClientProtocol = 'Pick 'Done ('Send String ('Var 'Z))

client :: Session '[] _ ('Rec ClientProtocol) 'Done Serialize IO ()
client = do
  enter

  pickR
  send "hello"
  vz

  pickR
  send "world"
  vz

  pickL


--------------------------------------------------------------------------------
-- Check client/server compatibility at compile time

clientServerIsDual :: AssertDual ServerProtocol ClientProtocol
clientServerIsDual = assertDual
