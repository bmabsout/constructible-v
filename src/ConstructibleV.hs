{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ViewPatterns           #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

module ConstructibleV
    ( vec
    , create
    , pattern (:>)
    , pattern Nil
    , module Linear.V
    ) where

import Linear.V
import qualified Data.Vector as V
import GHC.TypeLits
import Data.Kind as K
import Data.Proxy
newtype SizedList (n::Nat) a = SizedList [a]

sizedListCons :: a
              -> SizedList n a
              -> SizedList (n+1) a
sizedListCons h (SizedList t) = SizedList (h:t)

class Make n a func | func -> a n where
    make :: SizedList n a -> func

instance (ErrorIfUnequal n x, n~x)
    => Make n a (V x a) where
  make (SizedList l) = V $ V.fromList (reverse l)
  {-# INLINE make #-}

instance (Make (n+1) a f)
    => Make n a (a -> f) where
  make acc a = make (a `sizedListCons` acc)
  {-# INLINE make #-}

type family ErrorIfUnequal (a :: Nat) (b :: Nat)
    where
  ErrorIfUnequal a a = (() :: K.Constraint)
  ErrorIfUnequal a b =
    TypeError 
      ('Text "The created vector has size: " 
       ':<>: 'ShowType a
       ':$$: 'Text " While the expected size is: "
       ':<>: 'ShowType b)

empty :: SizedList 0 a 
empty = SizedList []

vec :: (Make 1 a f) => a -> f
vec = make empty
{-# INLINE vec #-}


type family Length (a :: [k]) = (n::Nat) where
  Length '[] = 0
  Length (x ': xs) = Length xs + 1


class ToValueLevel list where
  toValueLevel :: Num a
               => SizedList (Length list) a

instance ToValueLevel '[] where
  toValueLevel = empty

instance forall x xs.
         (KnownNat x, ToValueLevel xs)
      => ToValueLevel (x ': xs) where
  toValueLevel = fromIntegral (natVal (Proxy @x))
                   `sizedListCons` toValueLevel @xs


create :: forall list a .
          (ToValueLevel list, Num a)
       => V (Length list) a
create =
  (\(SizedList l) -> V $ V.fromList l)
    (toValueLevel @list)


pattern Nil :: V 0 a
pattern Nil <- _
  where Nil = V V.empty

uncons :: V (n+1) a -> (a, V n a)
uncons (V ht) = (V.head ht, V $ V.tail ht)

infixr 5 :>
pattern (:>) :: a -> V n a -> V (n+1) a
pattern h :> t <- (uncons -> (h, t))
  where (:>) h (V t) = V $ V.cons h t 