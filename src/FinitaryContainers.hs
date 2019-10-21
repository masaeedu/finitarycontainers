{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE AllowAmbiguousTypes, FunctionalDependencies, TypeFamilies #-}

module FinitaryContainers where

import Data.Proxy
import Data.Profunctor

import Fcf

data Nat = Z | S Nat

data Vec n a
  where
  VNil :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a

toList :: Vec n a -> [a]
toList VNil = []
toList (VCons x xs) = x : toList xs

instance Functor (Vec n)
  where
  fmap _ VNil = VNil
  fmap f (VCons x xs) = VCons (f x) (fmap f xs)

data Destructured (shape :: s -> Exp *) (arity :: s -> Exp Nat) (a :: *)
  where
  Destructured :: { index :: Proxy s, shape :: shape @@ s, contents :: Vec (arity @@ s) a } -> Destructured shape arity a

data Iso a b = Iso { fwd :: a -> b, bwd :: b -> a }

class Finitary shape arity f | f -> shape arity
  where
  destructuring :: Iso (f a) (Destructured shape arity a)

destructure :: Finitary s n f => f a -> Destructured s n a
destructure = fwd destructuring

restructure :: Finitary s n f => Destructured s n a -> f a
restructure = bwd destructuring

class Profunctor p => Shapely p
  where
  wander :: Finitary s n f => p a b -> p (f a) (f b)

type Traversal s t a b = forall p. Shapely p => p a b -> p s t

instance Shapely (->)
  where
  wander pab fa = case destructure fa of
    (Destructured p s xs) -> restructure $ Destructured p s $ pab <$> xs

instance Finitary (ConstFn ()) Pure []
  where
  destructuring = Iso fwd bwd
    where
    fwd :: [a] -> Destructured (ConstFn ()) Pure a
    fwd []       = Destructured Proxy () $ VNil
    fwd (x : xs) = case fwd xs of
      (Destructured _ _ c) -> Destructured Proxy () $ VCons x $ c

    bwd :: Destructured (ConstFn ()) Pure a -> [a]
    bwd (Destructured _ _ c) = toList c
