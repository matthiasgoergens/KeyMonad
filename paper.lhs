\documentclass[preprint]{sigplanconf}
%include polycode.fmt

%format :~: =  ":\sim:"
%format forall = "\forall"
%format . = ".\:"
\newcommand{\fmap}{\mathbin{<\!\!\!\mkern-0.4mu\raisebox{0.0pt}{\scalebox{0.8}{\$}}\mkern-0.4mu\!\!\!>}}
\begin{document}

%if False

\begin{code}
{-# LANGUAGE GADTs, RankNTypes, DataKinds, TypeOperators, NoMonomorphismRestriction #-}
import Data.Type.Equality
main = undefined

\end{code}
%endif

\section{The Key Monad}

The interface of our proposed extension, called the ``Key Monad'', is show in Figure \ref{interface}. The interface features two abstract types (types of which the constructors are not available to the user), |Key| and |KeyM|. The Key Monad, |KeyM|, gives the user the power to create fresh ``names'' of type |Key|. The only operation that is supported on this type is:
\begin{code}
testEquality :: Key s a -> Key s b -> Maybe (a :~: b)
\end{code}
This operation checks if the two given names are the same, and if they are it returns a proof that the types assocatied with the names, |a| and |b|, are the \emph{same} types. The proof that the types |a| and |b| are the same is a value of the following GADT:
\begin{code}
data a :~: b where
  Refl :: a :~: a
\end{code}

We can use there |Key|s to do similar things as with |Data.Typeable|, but \emph{without} the need |Typeable| constraints. For instance, we can create a variant of |Dynamic| using |Key|s instead of type representations. When given a key and value, we can ``lock up'' the value in a box which, like |Dynamic|, hides the type of its contents.
\begin{code}
data Box s where
  Lock :: Key s a -> a -> Box s
\end{code}

If we have a |Key| and a |Box|, we can try to unlock to the box to recover the value it contains.
\begin{code}
unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
   case testEquality k k' of
    Just Refl -> Just x
    Nothing   -> Nothing
\end{code}
If we used the right key, we get |Just| the value in the box, and we get |Nothing| otherwise.

To implement the |ST| monad we also need a heterogeneous map: a map that that maps keys to values the type corresponding to the key. To implement such maps efficiently, we use |IntMap|s and make use of the |hashKey| function.
\begin{code}
newtype KeyMap s = Km (IntMap (Box s))

empty :: KeyMap s
empty = Km IntMap.empty
\end{code}
In theory, multiple |Key|s can have the same hash, but in practice this is unlikely because this only occurs if we create more that $2^{32}$ keys. Hence for performance and simplicity, we map each integer only to a single box, but it is straightforward to adapt this code to a list of boxes if one is worried about integer overflow. Inserting a new value consists of creating a box from the key-value pair, and inserting this in the |IntMap| at the hash of the |Key|:
\begin{code}
insert :: Key s a -> a -> KeyMap s -> KeyMap s
insert k a (Km m) = Km $
  IntMap.insert (hashKey k) (Lock k a)
\end{code}
A lookup in a |KeyMap| consists of obtaining the box for the hash of the key, and then unlocking the box associated with the hash using the |Maybe| monad:
\begin{code}
lookup :: Key s a -> KeyMap s -> Maybe a
lookup k (Km m) =
  do  box <- IntMap.lookup (hashKey k) m
      unlock k box
\end{code}
Other operations, such as |update|, can be defined analogously.


Armed with our newly obtained |KeyMap|s, we can implement the |ST| monad. The implementation of |STRef|s is simply as an alias for |Key|s:
\begin{code}
type STRef s a = Key s a
\end{code}
We can now use the Key monad to create new keys, and use a |KeyMap|s to represent the current state of all created |STRef|s.
\begin{code}
newtype ST s a = ST (StateT (KeyMap s) (KeyM s) a)
  deriving (Functor,Applicative,Monad)
\end{code}
It is now straightforward to implement the operations for |STRef|s:
\begin{code}
newSTRef :: a -> ST s (STRef s a)
newSTRef v = do  k <- lift newKey
                 modify (insert k v)
                 return k

readSTRef :: STRef s a -> ST s a
readSTRef r = (fromJust . lookup r ) <$> get

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef k v = modify (insert k v)
\end{code}
Finally, the implementation of |runST| simply runs the monadic computation contained in the |ST| type:
\begin{code}
runST :: (forall s. ST s a) -> a
runST (Km m) = runKeyM (evalStateT empty m)
\end{code}

\begin{figure}

\begin{code}

type Key
type KeyM

newKey :: KeyM s (Key s a)
instance Monad (KeyM s )
instance TestEquality (Key s)
hashKey :: Key s a -> Int
runNameM :: (forall s. KeyM s a) -> a
\end{code}
\label{interface}
\end{figure}


\section{Converting between representations of binders and names}

What else can we do with the Key monad? One application is converting between representation of syntax with binders. when implementing a compiler or an interpreter for a programming language or (embedded) DSL in Haskell, one needs to represent the (abstract) syntax of the programming language. It is desirable to represent the syntax of a language with variable binding in a way that guarantees that transformation and interpretation of the syntax does not violate the scoping of variables. There exist a plethora of approaches to this problem, which can be partitioned into representations which use the binding of Haskell to represent binding, such as higher order abstract syntax (HOAS)\cite{hoas}, and techniques that do not, such as nested abstract syntax\cite{nestedhoas}. As we will show, there seems to be no way to translate syntax representions which use Haskell binders into representations which do not, but the Key monad allows us to cross this chasm.

As an example of a syntax representation that uses Haskell binder to represent binding, consider the Parametric Higher-order abstract syntax (PHOAS) \cite{phoas, ags, graphs} represenation of the (untyped) lambda calculus:
\begin{code}
data Phoas v
  = Var v
  | Lam (v -> Phoas v)
  | App (Phoas v) (Phoas v)
\end{code}
As an example of represting syntax using this datatype, the lambda term |\x y -> x| is represented by:
\begin{code}
Lam (\x -> Lam (\y -> Var x))
\end{code}
The reading of the type parameter |v| is the type of \emph{variables}. To guarantee well-scopedness, the type variable |v| should be abstract when constructing a lambda term. This can be enforced trough the type system by wrapping finished |PHOAS| term in the following  |newtype|:
\begin{code}
newtype Lambda = Lambda (forall v. Phoas v)
\end{code}
Our well-scoped lambda term |\x y -> x| can indeed be wrapped in this newtype, but terms which are not closed or well-scoped, are rejected by the type system:
\begin{code}
typeerr1 = Lambda (Var 1)
typeerr2 x = Lam (\y -> Var x)
\end{code}
While the type variable for variables is abstract when \emph{building} the lambda term, it can be arbitrary when interpreting or analyzing lambda terms. This makes it easy to define certain operations, such as an interpreter, while also making constructing lambda terms (relatively) easy.

Another technique is to not use Haskell binder to represent binding, and to use the type system to represent which variables are in scope\cite{nested,jp}. We present our own modern variant using Data Kinds and GADTs of this technique

\begin{code}
data Nat = S Nat | Z

data Index a where
  First :: Index (S Z)
  Next  :: Index n -> Index (S n)

data NLam n where
  Var :: Index n -> NLam n
  Lam :: NLam (S n) -> NLam n
  App :: NLam




The first category, consisting of higher order abstract syntax(HOAS)\cite{hoas} and its offshoots, represents binding using the binding of the host language. As an example of this technique, consider the a HOAS interface for the simply typed lambda calculus:

\begin{code}
class Hoas f where
  lam :: (f a -> f b) -> f (a -> b)
  app :: f (a -> b)   -> (f a -> f b)
\end{code}

As long a we form expressions only using the functions |lam| and |app|, we can be sure that the resulting lambda expression is well-scoped. We can ensure this by represting closed terms as follows:
\begin{code}
type ClosedHoas a = forall f. Hoas f => f a
\end{code}
For example, the function |\x y -> x| can now be written as follows:
\begin{code}
example :: ClosedHoas (x -> y -> x)
example = lam (\x -> lam (\y -> x))
\end{code}

As an example instance of the Hoas type class consider the parametric hoas datatype\cite{phoas} of the simply type lambda calculus, which uses a type argument |v| to represent variables.
\begin{code}
data PHoas v a where
  Var :: v a -> PHoas v a
  Lam :: (v a -> PHoas v b) -> PHoas v (a -> b)
  App :: PHoas v (a -> b) -> PHoas v a -> PHoas v b

instance Hoas (PHoas v) where
  lam f  = Lam (f . Var)
  app    = App
\end{code}

An advantage of this approach is that it is easy to use for defining syntax and it is straightforward to

\end{document}
