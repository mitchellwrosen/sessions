{-# language PartialTypeSignatures                #-}
{-# language RebindableSyntax                     #-}
{-# options_ghc -fno-warn-partial-type-signatures #-}

module PrintSession where

import Session

import Data.Serialize (Serialize)
import Data.String
import Prelude hiding ((>>=), (>>), return)


data Main = Main

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

type ServerProtocol
  = 'Label Main ('Offer '[ 'Done, 'Recv String ('Goto Main) ])

server :: Session '[] _ ServerProtocol 'Done Serialize IO ()
server = do
  label Main
  loop
 where
  loop =
    offer
      (return ())
      (do
        s <- recv
        lift (putStrLn s)
        goto Main
        loop)


--------------------------------------------------------------------------------
-- Print client

type ClientProtocol
  = 'Label Main ('Pick '[ 'Done, 'Send String ('Goto Main) ])

client :: Session '[] _ ClientProtocol 'Done Serialize IO ()
client = do
  label Main

  pick1
  send "hello"
  goto Main

  pick1
  send "world"
  goto Main

  pick0


--------------------------------------------------------------------------------
-- Check client/server compatibility at compile time

clientServerIsDual :: AssertDual ServerProtocol ClientProtocol
clientServerIsDual = assertDual
