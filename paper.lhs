\documentclass[preprint]{sigplanconf}
%include polycode.fmt
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{relsize}
\usepackage[a]{esvect}
\usepackage{marvosym}
\usepackage{graphicx}
\usepackage{wasysym}

\newcommand{\app}{\mathbin{<\!\!\!\!\mkern1.4mu\raisebox{-1.55pt}{\scalebox{0.9}{*}}\mkern1.4mu\!\!\!\!>}}
\newcommand{\aplus}{\mathbin{<\!\!\!\!\mkern1.4mu +\mkern1.4mu\!\!\!\!>}}
\newcommand{\fmap}{\mathbin{<\!\!\!\mkern-0.4mu\raisebox{0.0pt}{\scalebox{0.8}{\$}}\mkern-0.4mu\!\!\!>}}
%format :~: =  ":\sim:"
%format forall = "\forall"
%format . = ".\:"
%format >>> = "\mathbin{>\!\!\!>\!\!\!>}"
%format .>>= = "\cdot\!\!\!\bind"
%format .>> = "\cdot\!\!>\!\!\!>"
%format -< = "\prec"
%format >- = "\succ"
%format :. = "\circ"
%format procb = "\mathbf{proc}"
%format <$ = "\cmap"
%format <*> = "\app"
%format <$> = "\fmap"
%format <+> = "\aplus"



\title{Dynamic typing, Unconstrained!}
\authorinfo{Koen Claessen, Pablo Buiras, Atze van der Ploeg}{Chalmers University of Technology}
           {atze@@chalmers.se}
\begin{document}
\maketitle



\section{Introduction}


\section{The Key Monad}

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
\caption{The Key monad interface}
\label{interface}
\end{figure}

The interface of our proposed extension, called the ``Key Monad'', is show in Figure \ref{interface}. The interface features two abstract types (types of which the constructors are not available to the user), |Key| and |KeyM|. The Key Monad, |KeyM|, gives the user the power to create fresh ``names'' of type |Key|. The only operation that is supported on this type is:
\begin{code}
testEquality :: Key s a -> Key s b -> Maybe (a :~: b)
\end{code}
This function checks if the two given names are the same, and if they are a ``proof'' is returned that the types assocatied with the names, |a| and |b|, are the \emph{same} types. The proof that the types |a| and |b| are the same, is a value of the following GADT:
\begin{code}
data a :~: b where
  Refl :: a :~: a
\end{code}

We can use |Key|s to do similar things as with |Data.Typeable|, but \emph{without} the need for |Typeable| constraints. For instance, we can create a variant of |Dynamic| using |Key|s instead of type representations. When given a key and value, we can ``lock up'' the value in a box, which, like |Dynamic|, hides the type of its contents.
\begin{code}
data Box s where
  Lock :: Key s a -> a -> Box s
\end{code} If we have a |Key| and a |Box|, we can try to unlock to the box to recover the value it contains.
\begin{code}
unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
   case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing
\end{code}
If we used the right key, we get |Just| the value in the box, and we get |Nothing| otherwise.

To implement the |ST| monad using the |Key| monad, we also need a \emph{heterogeneous map}: a datastructure that that maps keys to values of the type corresponding to the key. To implement such maps efficiently, we use |IntMap|s and make use of the |hashKey| function.
\begin{code}
newtype KeyMap s = Km (IntMap (Box s))

empty :: KeyMap s
empty = Km IntMap.empty
\end{code}
In theory, multiple |Key|s can have the same hash, but in practice this is unlikely: this only occurs if we create more that $2^{32}$ keys. Hence for performance and simplicity, we map each integer only to a single box, but it is straightforward to adapt this code to use a list of boxes if one is worried about integer overflow. Inserting a new value consists of creating a box from the key-value pair, and inserting this in the |IntMap| at the hash of the |Key|:
\begin{code}
insert :: Key s a -> a -> KeyMap s -> KeyMap s
insert k a (Km m) = Km $
  IntMap.insert (hashKey k) (Lock k a)
\end{code}
A lookup in a |KeyMap| consists of obtaining the box for the hash of the key, and then unlocking the box with the key.
\begin{code}
lookup :: Key s a -> KeyMap s -> Maybe a
lookup k (Km m) =
  do  box <- IntMap.lookup (hashKey k) m
      unlock k box
\end{code}
Here, we employ the |Maybe| monad to sequence the operations, but the second operation, |unlock| cannot fail. Other operations, such as |update| and |(!)|, can be defined analogously.


Armed with our newly obtained |KeyMap|s, we can implement the |ST| monad. The implementation of |STRef|s is simply as an alias for |Key|s:
\begin{code}
type STRef s a = Key s a
\end{code}
We can now use the Key monad to create new keys, and use a |KeyMap|s to represent the current state of all created |STRef|s.
\begin{code}
newtype ST s a =
     ST (StateT (KeyMap s) (KeyM s) a)
  deriving (Functor,Applicative,Monad)
\end{code}
It is now straightforward to implement the operations for |STRef|s:
\begin{code}
newSTRef :: a -> ST s (STRef s a)
newSTRef v = do  k <- lift newKey
                 modify (insert k v)
                 return k

readSTRef :: STRef s a -> ST s a
readSTRef r = (fromJust :. lookup r ) <$> get

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef k v = modify (insert k v)
\end{code}
Finally, the implementation of |runST| simply runs the monadic computation contained in the |ST| type:
\begin{code}
runST :: (forall s. ST s a) -> a
runST (Km m) = runKeyM (evalStateT empty m)
\end{code}



Note that while the |Key| monad can be used to implement the |ST| monad, the reverse is not true. The problem is that there is no function:
\begin{code}
testEquality :: STRef s a -> STRef s b -> Maybe (a :~: b)
\end{code}
If we have such a function, then the |Key| monad is implementable with the |ST| monad (and vice versa). It is straightforward to implement the above function using |unsafeCoerce|:
\begin{code}
testEquality :: STRef s a -> STRef s b -> Maybe (a :~: b)
testEquality x y
   | x == y     = Just (unsafeCoerce Refl)
   | otherwise  = Nothing
\end{code}
Hence, another way to think of this paper is that we signal that the above function is safe, and that this allows us to do things which we could not do before.

\section{Embedding Proc notation}

\begin{figure}
  \rule{\columnwidth}{0.4pt}

\begin{code}
class Arrow a where
  arr    :: (x -> y) -> a x y
  (>>>)  :: a x y -> a y z -> a x z
  first  :: a x y -> a (x,z) (y,z)
\end{code}
\caption{The  arrow type class.}
\label{arrowsdef}
\end{figure}

The |Arrow| type class, recalled in Figure \ref{arrowsdef}, was introduced by Hughes\cite{arrows} as an interface that is like monads, but which allows for more static information about the constructed computations to be extracted. While monads allow intermediate values in the computation to be named (using regular lambda-abstractions), the arrow interface does not allow us to name intermediate values in the computation, instead computations must be written in \emph{point-free style}. This is alleviated by |proc| notation\cite{arrownot}, which requires specialized compiler support. In this section we show that with the power of the |Key| monad, we can name intermediate values in arrow computations directly using lambda abstractions, leading to an \emph{embedded} form of |proc| notation, which does not require specialized compiler support.

Before we show our embedded form of proc notation, let us first consider the difference between arrows and monad, by considering the difference between the state monad and the state arrow as an example(this example is taken from Lindley, Walder and Yallop \cite{idiomarrmonad}). The state monad and the state arrow have the following interfaces:
\begin{code}
newtype StateM s x = ...
instance Monad (StateM s) where

getM :: StateM s s
putM :: s -> StateM s ()


newtype StateA s x y = ...
instance Arrow (StateA s) where
getA :: StateA s () s
putA :: StateA s s ()
\end{code}
As a first example, consider generating a unique number, which can be expressed monadically as follows:
\begin{code}
uniqueM :: StateM Int Int
uniqueM = do  s <- getM
              putM (s + 1)
              return s
\end{code}
This can also be expressed using arrows, but since the arrow interface does not allow us to name intermediate values in the computation, the definition is in point-free style:
\begin{code}
uniqueA :: StateA Int () Int
uniqueA =  getA >>> arr (\x -> (x +1, x)) >>>
                first putA >>> arr snd
\end{code}
One can use |proc| notation to recover a more natural programming style, allowing intermediate values in arrow computations to be named. Using this notation, the unique number is obtained as follows:
\begin{code}
uniqueA :: StateA Int () Int
uniqueA = procb () ->
   do  x <- getA -< ()
       putA -< x + 1
       returnA -< x
\end{code}
This notation is supported by the GHC, which has fancy machinery to desugar it to a point-free definition.

To see the difference in expressive power of monad and arrows, consider  deciding what to do based on the current state, which can be done using the state monad:
\begin{code}
ifZeroM ::  StateM Int a -> StateM Int a -> StateM Int a
ifZeroM t f = do  s <- get
                  if s == 0 then t else f
\end{code}
It is impossible to express this for the state arrow\cite{idiomarrmonad}. The reason is that arrows provide no way to run a computation recieved as input, which is precisely the difference between monads and arrows: adding the ability to run an arrow computation obtained as input via the |ArrowApply| extension to arrows, leads to a type class equivalent to monads\cite{arrows}.
\begin{figure}
  \rule{\columnwidth}{0.4pt}

\begin{code}
class RelativeMonad m v where
  rreturn  :: v a -> m a
  (.>>=)   :: m a -> (v a -> m b) -> m b
  (.>>)    :: m a -> m b -> m b
  m .>> n = m .>>= (\_ -> n)
\end{code}
Relative monad laws:
\begin{code}
  m .>>= rreturn            = m
  rreturn x .>>= f          = f x
  m .>>= (x -> k x .>>= h)  = (m .>>= k) .>>= h
\end{code}

\caption{The relative monad class and its lwas.}
\label{relmonadfig}
\end{figure}

Recently,  Altenkirch, Chapman and Uustalu showed that in category theory, arrows are a special case of another generalization of monads, namely \emph{relative monads} \cite{relmonad}. We introduce a relative monad type class, corresponding to their categorial definition of relative monads, show in Figure \ref{relmonadfig}. The laws of the relative monad type class are the same as for the monad type class, replacing |return| by |rreturn| and |>>=| by |.>>=|. The difference is that relative monads have \emph{two} type parameters: one for the type of computations, |m|, and one for the type of the results of computations, |v|. With regular monads, the bind operation gives us a ``bare'' value of type |a|:
\begin{code}
(>>=) :: m a -> (a -> m b) -> m b
\end{code}
With relative monads, the operation |.>>=| gives the bound value wrapped in a type constructor |v|.

It straightforward to see that relative monads are a \emph{generalization} of monads: each monad gives rise to a relative monad in the following way:
\begin{code}
newtype Id a = Id a
instance Monad m => RelativeMonad m Id where
  rreturn (Id x) = return x
  m .>>= f = Id <$> m >>= f
\end{code}

More intrestingly, by chosing using an \emph{abstract} type constructor instead of |Id|, relative monads can also be used to limit the expressiveness of a language. We demonstrate this with a relative state monad, that does not allow us decide what to do based on the current state, i.e. it does not allow us to write |ifZeroM| above, making it exactly as powerfull as the state arrow. Consider the following interface:
\begin{code}
data StateRm v s a = ...

instance RelativeMonad (StateRm v s) v

getRm :: StateRm v s s
putRm :: v s -> StateRm v s

runStateRm :: (forall v.  Applicative v => StateRm v s x) ->
              (s,x)
\end{code}
Note that the |runStateRm| function ensures that the type variable |v| is abstract.

Using this interface, we can implement generating a unique number as follows:
\begin{code}
uniqueRm :: Applicative v => StateRm v Int Int
uniqueRm =
  getRm .>>= \s ->
  putM ((+ 1) <$> s)  .>>
  rreturn s
\end{code}
However, we cannot write |ifZeroM|, because there is no function:
\begin{code}
extract :: Applicative v => v a -> a
\end{code}
This state relative monad hence has exactly the same expressive power as the state arrow, but it allows us to name intermediate values using regular |lambda| abstractions, instead of relying on specialized compiler support.

Can we implement a relative monad that allows us to construct arrow computations by using the relative monad interface to name intermediate values? It turns out that we can, but only if we using the extra power of the key monad. This gives us an \emph{embedded} variant of proc notation: we can name intermediate values, without relying on compiler support. The translation of Altenkrich et al. of arrows to relative monads does not form a relative monad in Haskell because their bind has type:
\begin{code}
bind :: Arrow a => a s x -> (forall s. (s -> x) -> a s y) -> a s y
\end{code}
This \emph{is} the bind for a relative monad in category theory, but not in Haskell: the types do not match up. Because...?

Luckily, we can use the Key monad to obtain a construction similar to that of Altenkirch et al, which does allow us to name intermediate values in arrow computations using the relative monad interface. The interface of this construction is as follows:
\begin{code}
newtype Cage s = ...
newtype Arm a s x = ...

instance  Arrow a =>
          RelativeMonad (Arm a s) (Cage s) where ...

toRm :: Arrow a   =>
   a x y -> (forall s. Cage s x -> Arm a s y)

fromRm :: Arrow a =>
  (forall s. Cage s x -> Arm a s y) -> a x y
\end{code}
As example, consider the following arrow computation in |proc| notation:
\begin{code}
addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = procb z -> do
   x <- f -< z
   y <- g -< z
   returnA -< x + y
\end{code}
Which becomes the following using the relative monad interface:
\begin{code}
(>-) :: Arrow a => Cage s x -> a x y -> Arm a s y
v >- a = toRm a v

addRm :: Arrow a => a b Int -> a b Int -> a b Int
addRm f g = fromRm $ \z ->
    z >- f .>>= \x ->
    z >- g .>>= \y ->
    rreturn ((+) <$> x <*> y)
\end{code}
Aside from flipping the direction of reading, we must now also use the applicative interface to massage values.


How do we implement this interface? We use |Key|s to represent a variable bound by |.>>=|, and |KeyMap| to represent an enviroment, i.e. a mapping of variables to values. A |Cage| is then an expression, i.e. a function from enviroment to value:
\begin{code}
newtype Cage s x = Cage (KeyMap s -> x)
   deriving (Functor,Applicative)
\end{code}
A variable can be easily converted to an expression:
\begin{code}
toExp :: Key s a -> Cage s a
toExp k = Cage (\e -> e !  k)
\end{code}



Since each |.>>=| introduces a new variable, our implementation of the arrow relative monad, |Arm|, must be able to create new keys, and result in an arrow computation:
\begin{code}
newtype Arm a s x =
   Arm { getArm :: KeyM s (a (KeyMap s) x) }
\end{code}
The arrow computation that is the result of the |KeyM| computation is an arrow computation from a enviroment, i.e. |KeyMap|, to a value.
If we have the expression for the input, we can convert any arrow to this type by first evaluting the expression using the enviroment, and then passing it to the arrow:
\begin{code}
toArm :: Arrow a => a x y -> Cage s x -> Arm a s y
toArm a (Cage f) = Arm (pure (arr f >>> a))
\end{code}
To implement |.>>=|, we need to be able to extend an enviroment.
If we have a variable |k| for the result of the computation of type |x|, then we can convert an arrow computation of type |a (KeyMap s) x| to an arrow computation that extends the enviroment with a new mapping of the variable |k| to the value of type |x|:
\begin{code}
extend :: Arrow a => a (KeyMap s) y -> Key s y
     -> a (KeyMap s) (KeyMap s)
extend a k = a &&& arr id >>> arr (uncurry (insert k))
\end{code}
We can now implement the relative monad interface as follows:
\begin{code}
instance Arrow a =>
  RelativeMonad (Arm a s) (Cage s) where
  rreturn (Cage f)   = Arm (pure (arr f))
  m .>>= f  = Arm $
    do  al <- getArm m
        k <- newKey
        ar <- getArm (f (toExp k))
        pure (extend al k >>> ar)
\end{code}
The implementation of |.>>=| first evaluates the |KeyM| computation of |m|, and then creates a new name (|Key|) for its result. This name is converted to an expression and passed to |f|, and the resulting |KeyM| computation is run. We then compose the two obtained arrows, |al|, and |ar|, by extending the enviroment given as input to |al| with the result of |al|, using name |k| and passing the resulting enviroment as input to |ar|.

For the final piece of the puzzle, |fromRm| we create a variable for the input to the arrow, and feed it to the function in the same way as for |.>>=|:
\begin{code}
fromArm :: Arrow a => (forall s. Cage s x -> Arm a s y)
         -> a x y
fromArm f = runKeyM $
     do k <- newKey
        a <- getArm (f (toExp k))
        return (arr (singleton k) >>> a)
\end{code}


\subsection{Inverse translation}

While every monad gives rise to an arrow, not every relative monad gives rise to an arrow. In particular, relative monads give rise to an arrow if the type for results of computations |v| supports the |Applicative| interface. For regular monads, |v = Id|, which trivially supports |Applicative|. This translation is a generalization of the |Kleisli| construction which gives an arrow for each monad:
\begin{code}
newtype RelKleisli m v a b =
   RelKleisli {runK :: v a -> m b }

instance (Applicative v, RelativeMonad m v) =>
    Arrow (RelKleisli m v) where
  arr f = RelKleisli $ \x -> rreturn (f <$> x)

  f >>> g = RelKleisli $ \x -> runK f x .>>= (runK g)

  first a = RelKleisli $ \t ->
     let x = fst <$> t
         y = snd <$> t
      in runK a x .>>= \x' ->
          rreturn ((,) <$> x' <*> y)
\end{code}

\subsection{Correctness}

A very similar construction has been introduced by Lindley, Wadler, and Yallop \cite{arrowcalc}, who introduce the \emph{arrow calculus}, which works similarly to our |Arm| construction. The main difference is that their arrow calculus is not embedded in Haskell, but theoretical and that in the arrow calculus there is no distiction between |Cage s a| and |a|, because their language does not allow the observation of values in (what can be seen as) relative monad syntax, omitting the need to make values abstact by putting them in |Cage|s.  Aside from this minor difference, the mapping of our constructs to theirs is as follows: \\[0.5cm]
\begin{tabular}{l || l}
Arrow calculus & Embedded proc \\
\hline
Types & \\
\hline
$ x\: !\: t$ & |x :: Arm a s t| \\
$ x : t $ & | x :: t| (in pure context) \\
$ x : t $ & |x :: Cage s t| (in arrow context)\\
Expressions & \\
\hline
$\lambda^{\bullet}x . Q$ & |fromArm (\x -> Q)| \\
$l \bullet m$ & |m .>>= toArm l| \\
$\mathtt{let}\: x \Leftarrow p\: \mathtt{in}\: Q$ & |p .>>= \x -> Q| \\
$[x]$ & |rreturn x| \\
\end{tabular}\\[0.5cm]
Lindley et al. also give laws for their arrow calculus, which are the relative monad laws plus two additional laws, which can be translated to our setting: :\\[0.5cm]
\begin{tabular}{l l}
$(\beta^{\rightsquigarrow})$  & $(\lambda^{\bullet}x . q) \bullet p = \mathtt{let}\: x \Leftarrow p\: \mathtt{in}\: q$ \\
translation : & |P .>>= toArm (fromArm (\x -> Q))| \\
& | = P .>>= \x -> Q | \\
$(\eta^{\rightsquigarrow})$ & $ \lambda^{\bullet}x . (l \bullet [x])) = l$ \\
translation &  |fromArm (\x -> rreturn x .>>= toArm Q) = Q | \\
\end{tabular} \\[0.5cm]
In our setup, these can in turn be proved from the relative monad laws and the following simpler laws: \\[0.5cm]
\begin{tabular}{l l}
$\mathit{iso}^{\rightarrow}$ & |toArm (fromArm f) = f | \\
$\mathit{iso}^{\leftarrow}$ & |fromArm (toArm q) = q| \\
\end{tabular}\\[0.5cm]

Lindley et al. give a translation of their arrow calculus to arrows, which is essentially the same as our implementation of the |Arm| interface. They also give a translation from arrows to the arrow calculus, which is essentially the same as our |RelKleisli| construction. Lindey et al. prove of the equational correspondence of their arrow calculus and arrows. They do by showing that the arrow calculus laws follow from the translation to arrows and the arrow laws, and the arrow laws follow from the arrow calculus laws and the translation of arrows to the arrow calculus. Because they constructions is essentially the same it should be possible to adapt their proof of equational correspondence to our setting.






\subsection{ArrowPlus and Relative monad plus}

\subsection{ArrowLoop and Relative monad Fix}

\subsection{Using monad for relative monads}

\cite{bjorn}




\section{Converting between representations of binders and names}

What else can we do with the Key monad? The Key monad allows us to associate types with ``names'' (|Key|s), and to see that if two names are the same, then their associated types are also the same. One use case for this is when dealing with representations of syntax with binders, as we will show next.

When implementing a compiler or an interpreter for a programming language or (embedded) DSL in Haskell, one needs to represent the (abstract) syntax of the programming language. It is desirable to construct the terms of a language with variable binding. in a way that guarantees that the terms are well-scoped. There are broadly two approaches to this problem, namely higher order abstract syntax (HOAS)\cite{hoas}, and  nested abstract syntax\cite{nested}. As we will show, there seems to be no way to translate terms created with HOAS to nested abstract syntax, but the Key monad allows us to cross this chasm.

In HOAS, lambda terms are constructed using the methods from the following type class:
\begin{code}
class Hoas f where
  lam :: (f a -> f b)  -> f (a -> b)
  app :: f (a -> b)    -> (f a -> f b)
\end{code}
For example, the lambda term |(\x y -> x)| can be constructed as follows:
\begin{code}
example :: Hoas f => f (x -> y -> x)
example = lam (\x -> lam (\y -> x))
\end{code}
The attractive thing of HOAS is that we use Haskell binding to construct syntax, and that terms built using the HOAS interface are always well-scoped, because of the well-scopeness of Haskell bindings.

An example of a syntax representation that implements this interface is Parametric Higher-order abstract syntax (PHOAS) \cite{phoas, ags, graphs}. The PHoas represenation of typed lambda terms is:
\begin{code}
data Phoas v a where
  PVar :: v a -> Phoas v a
  PLam :: (v a -> Phoas v b) -> Phoas v (a -> b)
  PApp :: Phoas v (a -> b) -> Phoas v a -> PHoas b

instance Hoas (Phoas v) where
  lam f  = PLam (f . Var)
  app    = PApp
\end{code}
The reading of the type parameter |v| is the type of \emph{variables}.

The second way to ensure well-scopedness is to use the type system to represent the enviroment of variables which are in scope\cite{nested,jp}. Terms which are not well-scoped will then lead to a type error, instead of a scoping error as with Hoas. We present our own modern variant of this technique using Data Kinds and GADTs, but it is essentially the same as presented by Bird and Paterson \cite{nested} . We start by using the standard GADTs for heterogenous lists and indexes in the lists:
\begin{code}
data HList l where
  HNil   :: HList []
  HCons  :: h -> HList t -> HList (h : t)

data Index l a where
  HHead  :: Index (h : t) h
  HTail  :: Index t x -> Index (h : t) x
\end{code}
If we think of a |HList l| as an enviroment, where |l| is the list of types in the enviroment, then |Index l a| is a de Bruijn index in such an enviroment, of type |a|. We can use this insight to represent lambda terms as follows:
\begin{code}
data NSyn l a where
  NVar  :: Index l a -> NSyn l a
  NLam  :: NSyn (a : l) b -> NSyn l (a -> b)
  NApp  :: NSyn l (a -> b) -> NSyn l a -> NSyn l b
\end{code}
The reading of the type variable |l| is the list of types which are in the enviroment, and hence the enviroment is extended in the body of a lambda term. A closed term of type |a| has type |NSyn [] a|.

This technique ensures that all variables are well scoped, but when writing lambda expressions, we must now manually write de Bruijn indexes for variables. For example, the lambda term |(\x y -> x)| becomes:
\begin{code}
nsexample :: NSyn [] (x -> y -> x)
nsexample = NLam (NLam (HTail HHead))
\end{code}
There are techniques which alleviate the need to manually use the de Bruijn indexes\cite{jp}, which rely on type-level computation to do the lookup of variables. These make the user-interface a bit more complicated and lead to type-errors for scoping errors, instead of regular scoping errors. Because in nested syntax a binding changes the type of the syntax represenation, there seem to be no instance for |Hoas| for |NSyn|.

The well-scopedness of variables in an |NSyn| value follows from the fact that the value is well-typed. With |Hoas|, the well-scopedness relies on the meta-level (i.e. not formalized through types) argument that no well-scoped values can be created by using the |Hoas| interface. The internal (i.e. formalized through types) well-scopedness of |NSyn| allows interpretations of syntax which seem to not be possible if we are using terms constructed with HOAS. As an example of this, consider translating lambda terms to \emph{cartesian closed category} combinators (the categorical version of the lambda calculus). This can be done if the lambda terms are given as |NSyn| values, as demonstrated in Figure \ref{ccc}. Without the Key monad, there seem to be no way to do the same for terms constructed with the HOAS terms (in Haskell).

We want to have our cake and eat it two: we want to build terms using the simple |Hoas| interface, and then convert them to a representation where the types in the enviroment are explicit. In other words, we want a translation function of the following type:
\begin{code}
makeMorePrecise :: (forall f. Hoas f => f x) -> NSyn [] x
\end{code}
There seem to be no way to implement this function without the added power of the Key monad. With the Key monad we \emph{can} implement this function, which transitively also allows us do anything with HOAS terms what we can do with nested syntax terms, such as translating to cartesian closed categories.

To facilitate this translation, let us introduce a representation of lambda terms where |Key|s are used as variables:
\begin{code}
data KLam s a where
  KVar :: Key s a -> KLam s a
  KLam :: Key s a -> KLam s b -> KLam s (a -> b)
  KApp :: KLam s (a -> b) -> KLam s a -> KLam s b
\end{code}
Here the arguments to the constructor for lamdba abstraction, |KLam|, are the fresh variable for the argument, of type |Key|, and the body of the lambda abstraction. To provide an instance of |Hoas| for this representation of lambda terms, we wrap a |KeyM| computation resulting in a |KLam| value, in a single type:
\begin{code}
newtype KeyMLam s a = KL (KeyM s (KeyLam s a))

instance Hoas (KeyMLam s) where
  lam f = KL $
     do  k <- newKey
         let KL m = f (KL (pure $ KVar k))
         b <- m
         return $ KLam k b
  app (KL f) (KL x) = KL $ KApp <$> f <*> x
\end{code}
The |lam| function creates a new key for the lambda abstraction, and passes it to the body.

We will now show how we can create a function of type:
\begin{code}
toNSyn :: KeyLam s a -> NSyn [] a
\end{code}
Since |KeyMLam| implements |Hoas| we can then implement |makeMorePrecise| as follows:
\begin{code}
makeMorePrecise :: (forall f. Hoas f => f x) -> NSyn [] x
makeMorePrecise (KL m) = runKeyM (toNSyn <$> m)
\end{code}
For the |toNSyn| function, we need a variant of the |Box| we saw previously:
\begin{code}
data FBox s f where
  FLock :: Key s a -> f a -> FBox s f

funlock :: Key s -> FBox s f -> Maybe (f a)
funlock k (FLock k' x) =
  case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing
\end{code}
The difference with |Box| is that we now store values of type |f a| instead of values of type |a| in the box. We can provide a variant of |fmap| for this container:
\begin{code}
class PFunctor p where
  pfmap :: (forall x. f x -> g x) -> p f -> p g

instance PFunctor (FBox s) where
  pfmap f (FLock k x) = FLock k (f x)
\end{code} We also need a variant of the |KeyMap|, where we store |FBox|es instead of regular boxes:
\begin{code}
newtype FKeyMap s f = FKm (IntMap (FBox s f))
insert :: Key s a -> f a -> FKeyMap s f  -> FKeyMap s f
lookup :: Key s a -> FKeyMap s f -> Maybe (f a)
\end{code}
We also provide an instance for |PFunctor| for this datatype:
\begin{code}
instance PFunctor (FKeyMap s) where
  pfmap f (FKm m) = FKm (fmap (pfmap f) m)
\end{code}

We store the current ``enviroment'' as a |FKeyMap| mapping each |Key| to an |Index| in the current enviroment. When we enter a lambda-body, we need to extend the enviroment with a new name mapping to the ``de Bruijn index'' |HHead|, and add one lookup step to each other ``de Bruijn index'' currently in the |FKeyMap|. This is be done as follows:
\begin{code}
extend :: Key s h -> FKeyMap s (Index t) ->
            FKeyMap s (Index (h : t))
extend k m = insert k HHead (pfmap HTail m)
\end{code}
With this machinery in place, we can translate |KeyLam| to |NSyn| as follows:
\begin{code}
toNSyn :: KeyLam s a -> NSyn [] a
toNSyn = go empty where
  go :: HFMap s (HIndex l) -> KeyLam s x -> NSyn l x
  go e (KVar v)   = NVar (e ! v)
  go e (KLam k b) = NLam (translate (extend k e) b)
  go e (KApp f x) = NApp (translate e f) (translate e x)
\end{code}






\begin{figure}
\begin{code}
toClosed :: CCC c => NSyn [] (x -> y) -> c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => NSyn l y -> TList l (c x) -> c x y
  go (NVar x)    e = findex e x
  go (NLam b)    e = curry $
                    go b (TCons snd (tmap (. fst) e))
  go (NApp f x)  e = uncurry (go f e) . prod id (go x e)

class Category c => CCC c where
    prod     :: c x a -> c x b -> c x (a,b)
    fst      :: c (a,b) a
    snd      :: c (a,b) b
    curry    :: c (a,b) x -> c a (b -> x)
    uncurry  :: c a (b -> x) -> c (a,b) x

data TList l f where
  TNil   :: TList [] f
  TCons  :: f h -> TList t f -> TList (h : t) f

tindex :: TList l f -> Index l x -> f x
tindex (TCons h _) HHead     = h
tindex (TCons _ t) (HTail i) = tindex t i

instance PFunctor (TList l) where
  pfmap f TNil        = TNil
  pfmap f (TCons h t) = TCons (f h) (tmap f t)
\end{code}
\label{ccc}
\caption{Translating lambda terms to cartesian closed categories.}

\end{figure}

\section{Approximating the |Key| monad}

The |Key| monad seems to be a perfectly safe thing, but it seems that it is not expressible in Haskell directly.

\bibliographystyle{apalike}
\bibliography{refs}

\end{document}
