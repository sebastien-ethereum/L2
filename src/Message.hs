{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}


--------------------------------------------------------------------------------
--
-- Strongly typed embedding of Dolev-Yao model with signatures
--
-- Author: sebastien@ethereum.org
--
--------------------------------------------------------------------------------


module Message where


import GHC.TypeLits


type Lit = Nat


type Key = String


data Message :: * where
  Lit  :: Lit -> Message
  Key  :: Key -> Message
  Pair :: Message -> Message -> Message
  Sign :: Key -> Message -> Message


type Context = [Message]


data (∈) :: Message -> Context -> * where
  Z :: -----------
       m ∈ (m : g)

  S :: m ∈ g
       -----------
    -> m ∈ (n : g)


data (⊩) :: Context -> Message -> * where
  Hyp    :: m ∈ g
            -----
         -> g ⊩ m

  Subst  :: g ⊩ m
         -> (m : g) ⊩ n
            -----------
         -> g ⊩ n

  LitI   :: KnownNat x    -- example: `LitI (Proxy 42)`
         => proxy x
            ----------
         -> g ⊩ 'Lit x

  PairI  :: g ⊩ m
         -> g ⊩ n
            -------------
         -> g ⊩ 'Pair m n

  PairE1 :: g ⊩ 'Pair m n
            -------------
         -> g ⊩ m

  PairE2 :: g ⊩ 'Pair m n
            -------------
         -> g ⊩ n

  SignI  :: g ⊩ 'Key k
         -> g ⊩ m
            -------------
         -> g ⊩ 'Sign k m

  SignE  :: g ⊩ 'Sign k m
            -------------
         -> g ⊩ m


data Signature :: * -> * where
  LitI'   :: Integer -> Signature a
  PairI'  :: (a, a) -> Signature a
  PairE1' :: a -> Signature a
  PairE2' :: a -> Signature a
  SignI'  :: (a, a) -> Signature a
  SignE'  :: a -> Signature a


type Algebra f a = f a -> a


data Fixpoint f = In {out :: f (Fixpoint f)}


trivial :: Algebra Signature (Fixpoint Signature)
trivial = In


data Environment :: Context -> * -> * where
  Nil  :: Environment '[] a
  Cons :: a -> Environment g a -> Environment (m : g) a


eval :: Algebra Signature a -> g ⊩ m -> Environment g a -> a
eval _   (Hyp Z)      (Cons x _)   = x
eval alg (Hyp (S n))  (Cons _ env) = eval alg (Hyp n) env
eval alg (Subst d d') env          = eval alg d' (Cons (eval alg d env) env)
eval alg (LitI proxy) _            = (alg . LitI') (natVal proxy)
eval alg (PairI d d') env          = (alg . PairI') (eval alg d env, eval alg d' env)
eval alg (PairE1 d)   env          = (alg . PairE1') (eval alg d env)
eval alg (PairE2 d)   env          = (alg . PairE2') (eval alg d env)
eval alg (SignI d d') env          = (alg . SignI') (eval alg d env, eval alg d' env)
eval alg (SignE d)    env          = (alg . SignE') (eval alg d env)
