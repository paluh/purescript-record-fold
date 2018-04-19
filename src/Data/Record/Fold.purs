module Data.Record.Fold
  ( class Step
  , class FoldR
  , class Fold
  , class FoldMap
  , ApplyS
  , applyTo
  , AppCat
  , CollectS
  , collect
  , EqS
  , fold
  , foldR
  , FoldMapS
  , length
  , MapS
  , rEq
  , rMap
  , rShow
  , ShowS
  , step
  ) where

import Prelude

import Data.Array (cons)
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.Record (get)
import Data.Record.Builder (Builder, build, insert)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (Tuple(..))
import Type.Row (class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)

class Step stepper (lbl :: Symbol) val step | val -> step where
  step :: stepper -> (SProxy lbl) -> val -> step

class FoldR stepper (list :: RowList) (row :: # Type) fold | list -> fold where
  foldR :: stepper -> (RLProxy list) -> Record row -> fold

instance foldRowCons
  ::
  ( Step stepper lbl val (step a b)
  , IsSymbol lbl
  , RowCons lbl val rest row
  , Semigroupoid step
  , FoldR stepper tail row (step b c)
  ) => FoldR stepper (Cons lbl val tail) row (step a c) where
  foldR name _ record =
    let
      key = SProxy :: SProxy lbl
      tail = RLProxy :: RLProxy tail
      res = foldR name tail record
    in step name key (get key record) >>> res

instance foldRowNil
  ::
  ( Category step
  ) => FoldR name Nil r (step a a) where
  foldR name _ _ = id


class Fold stepper a fold | a -> fold where
  fold :: stepper -> a -> fold

instance foldRecord
  ::
  ( RowToList row list
  , FoldR stepper list row fold
  ) => Fold stepper (Record row) fold where
  fold stepper r = foldR stepper (RLProxy :: RLProxy list) r


newtype FoldMapS m = FoldMapS (forall a n. IsSymbol n => SProxy n ->  a -> m)

instance foldMapStep :: (IsSymbol lbl, Semigroup m) => Step (FoldMapS m) lbl a (m -> m) where
  step (FoldMapS f) s a m = f s a <> m

class (Fold (FoldMapS m) r (m -> m)) <= FoldMap r m

rFoldMap
  ::  forall m r
   . Monoid m
  => FoldMap r m
  => (forall a n. IsSymbol n => SProxy n -> a -> m) -> r -> m
rFoldMap f r = fold (FoldMapS f) r $ mempty

length
  :: forall r
   . FoldMap r (Additive Int)
  => r -> Int
length = unwrap <<< rFoldMap (const $ const $ Additive 1)

labels
  :: forall r
   . FoldMap r (Array String)
  => r -> Array String
labels = rFoldMap (\s _ -> [reflectSymbol s])


type Res = Array (Tuple String String)
data ShowS = ShowS

instance showStep ::
  ( Show a
  , IsSymbol lbl
  ) => Step ShowS lbl a ((Array (Tuple String String)) -> (Array (Tuple String String))) where
  step _ sym val acc = cons (Tuple (reflectSymbol sym) (show val)) acc

rShow
  :: forall r
   . Fold ShowS r (Res -> Res)
  => r -> Res
rShow rec = fold ShowS rec $ []


data MapS (f :: Type -> Type) = MapS (forall a. a -> f a)

instance mapStep ::
  ( IsSymbol lbl
  , RowCons lbl (f a) tail row
  , RowLacks lbl tail
  ) => Step (MapS f) lbl a (Builder (Record tail) (Record row)) where
  step (MapS f) lbl val = insert lbl (f val)

rMap
  :: forall f r res
   . Fold (MapS f) r (Builder {} (Record res))
  => (forall a. a -> f a) -> r -> Record res
rMap f r =
  let
    builder = fold (MapS f) r
    res = build builder {}
  in res


data ApplyS a = ApplyS a

instance applyStep ::
  ( IsSymbol lbl
  , RowCons lbl b tail row
  , RowLacks lbl tail
  ) => Step (ApplyS a) lbl (a -> b) (Builder (Record tail) (Record row)) where
  step (ApplyS c) lbl f = insert lbl (f c)

applyTo
  :: forall a r res
   . Fold (ApplyS a) r (Builder {} (Record res))
  => a -> r -> Record res
applyTo v r =
  let
    res = build (fold (ApplyS v) r) {}
  in res


data CollectS = CollectS

newtype AppCat app cat a b = AppCat (app (cat a b))

instance semigroupoidAppCat :: (Semigroupoid cat, Applicative app) => Semigroupoid (AppCat app cat) where
  compose (AppCat a1) (AppCat a2) = AppCat $ (<<<) <$> a1 <*> a2

instance categoryAppCat :: (Category cat, Applicative app) => Category (AppCat app cat) where
  id = AppCat (pure id)

instance collectStep ::
  ( IsSymbol lbl
  , RowCons lbl a tail row
  , RowLacks lbl tail
  , Apply f
  ) => Step CollectS lbl (f a) (AppCat f Builder (Record tail) (Record row)) where
  step _ lbl a = AppCat $ insert lbl <$> a

collect
  :: forall f r res
   . Applicative f
  => Fold CollectS r (AppCat f Builder {} (Record res))
  => r -> f (Record res)
collect r =
  let
    AppCat builder = fold CollectS r
    res = build <$> builder <*> pure {}
  in res

data EqS = EqS

instance eqStep ::
  ( RowCons lbl a r' r
  , IsSymbol lbl
  , Eq a
  ) => Step EqS lbl a (AppCat ((->) (Record r)) (->) Boolean Boolean) where
  step _ lbl val = AppCat \other res -> res && get lbl other == val

rEq
  :: forall r
   . Fold EqS r (AppCat ((->) r) (->) Boolean Boolean)
  => r -> r -> Boolean
rEq r1 r2 =
  let
    AppCat run = fold EqS r1
  in
    run r2 true

