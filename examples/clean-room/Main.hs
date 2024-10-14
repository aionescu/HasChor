{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}

{-# LANGUAGE BlockArguments, DataKinds, DerivingStrategies, GADTs, ImpredicativeTypes, LambdaCase, ParallelListComp #-}
module Main where

import Data.Foldable(fold)
import Data.Function((&))
import Data.Functor(void)
import Data.Proxy(Proxy(..))
import Data.SOP.BasicFunctors(mapKK)
import Data.SOP.Classes(HCollapse(..), hmap, hsequenceK)
import Data.SOP.Constraint(All)
import Data.SOP.NP(NP(..))
import GHC.TypeLits(KnownSymbol, withSomeSSymbol, SSymbol, withKnownSymbol)
import System.Environment(getArgs)

import Choreography
import Choreography.Location
import Choreography.Location.Multi

-- Schema stuff (just placeholders for now)

newtype Dataset = Dataset [Int]
  deriving stock (Show, Read)
  deriving newtype (Semigroup, Monoid)

data Schema = Schema
  deriving stock (Show, Read)

data Query
  = Len
  | Sum
  | Avg
  | Min
  | Max
  deriving stock (Eq, Ord, Show, Read)

loadDataset :: KnownSymbol l => Proxy l -> IO Dataset
loadDataset l = Dataset . fmap read . lines <$> readFile ("examples/clean-room/datasets/" <> toLocTm l <> ".txt")

getSchema :: Dataset -> Schema
getSchema _ = Schema

mergeSchemas :: [Schema] -> Schema
mergeSchemas _ = Schema

getQuery :: KnownSymbol l => Proxy l -> Schema -> IO Query
getQuery l _ =
  pure
    case toLocTm l of
      "c1" -> Avg
      "c2" -> Avg
      "c3" -> Min
      "c4" -> Sum
      _    -> error "query: Unknown location"

agreeWithQueries :: KnownSymbol l => Proxy l -> [Query] -> IO Bool
agreeWithQueries l qs =
  pure
    case toLocTm l of
      "c1" -> True
      "c2" -> not $ Len `elem` qs && Avg `elem` qs
      "c3" -> not $ Min `elem` qs && Max `elem` qs
      "c4" -> length qs < 10
      _    -> error "agree: Unknown location"

mergeDatasets :: [Dataset] -> Dataset
mergeDatasets = fold

runQuery :: Dataset -> Query -> IO Int
runQuery (Dataset ds) q =
  pure
    case q of
      Len -> length ds
      Sum -> sum ds
      Avg -> sum ds `quot` length ds
      Min -> minimum ds
      Max -> maximum ds

-- Main choreography

cleanRoom :: (KnownSymbol server, All KnownSymbol clients) => Proxy server -> NP Proxy clients -> Choreo IO ()
cleanRoom server clients = do
  -- Every client loads their dataset, computes their schema, and sends it to the server
  datasets <- multilocally clients \l _ -> loadDataset l
  schemas <- (clients, \_ unwrap -> pure $ getSchema $ unwrap datasets) *~~> server

  -- Server merges the schemas and broadcasts the final schema
  finalSchema <- (server, \unwrap -> pure $ mergeSchemas $ hcollapse $ unwrap schemas) ~~>* clients

  -- Based on the final schema, each client computes what query it wants to run, and sends it back to the server
  queriesS <- (clients, \l unwrap -> getQuery l $ unwrap finalSchema) *~~> server

  -- Server broadcasts the list of queries to all clients
  queries <- (server, \unwrap -> pure $ hcollapse $ unwrap queriesS) ~~>* clients

  -- Each client locally decides if they agree with everyone else's queries, and sends back a response
  agreements <- (clients, \l unwrap -> agreeWithQueries l $ unwrap queries) *~~> server

  -- Server branches on the responses
  cond' (server, \unwrap -> pure $ and $ hcollapse $ unwrap agreements) \case
    False -> void $ multilocally clients \_ _ -> print "Disagreement"
    True -> do -- Everyone agrees, proceed
      -- Everyone sends their dataset to the server
      datasetsS <- datasets *~> server

      -- Server locally merges the datasets and runs all the queries
      resultsS <- locally server \unwrap -> do
        let dataset = mergeDatasets $ hcollapse $ unwrap datasetsS
        hsequenceK $ hmap (mapKK $ runQuery dataset) $ unwrap queriesS

      -- Server sends the result of each query "pointwise"
      results <- (server, resultsS) ~>. clients

      -- Clients consume the received query results
      void $ multilocally clients \_ unwrap -> print $ unwrap results

-- Running the choreography

withProxy :: String -> (forall s. KnownSymbol s => Proxy s -> a) -> a
withProxy s f = withSomeSSymbol s \(ss :: SSymbol s) -> withKnownSymbol ss $ f @s Proxy

withProxies :: [String] -> (forall ss. All KnownSymbol ss => NP Proxy ss -> a) -> a
withProxies [] f = f Nil
withProxies (s : ss) f =
  withProxy s \s ->
    withProxies ss \ss ->
      f $ s :* ss

httpConfig :: [String] -> HttpConfig
httpConfig ls = mkHttpConfig [(l, ("localhost", port)) | l <- ls | port <- [3000..]]

main :: IO ()
main = do
  self : ls@(server : clients) <- getArgs
  runChoreography (httpConfig ls) (cleanRoom & withProxy server & withProxies clients) self
