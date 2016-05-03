\documentclass[preprint]{sigplanconf}
%include polycode.fmt
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{relsize}
\usepackage[a]{esvect}
\usepackage{marvosym}
\usepackage{graphicx}
\usepackage{wasysym}
\usepackage{multirow}
\usepackage{array}
\newcolumntype{L}[1]{>{\raggedright\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{C}[1]{>{\centering\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{R}[1]{>{\raggedleft\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}


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
%format E1 = "E_1"
%format E2 = "E_2"
%format EN = "E_n"
%format uncurryn = "\mathit{uncurry}_n"
\title{Dynamic typing, Unconstrained!}
\authorinfo{Koen Claessen, Pablo Buiras, Atze van der Ploeg}{Chalmers University of Technology}
           {atze@@chalmers.se}
\begin{document}
\maketitle



\section{Introduction}


\section{The Key Monad}




\begin{figure}
  \rule{\columnwidth}{0.4pt}
\begin{code}
type Key
type KeyM

instance Monad (KeyM s)

newKey :: KeyM s (Key s a)

testEquality :: KeyM s a -> Key s b -> Maybe (a :~: b)

data a :~: b where
  Refl :: a :~: a

runKeyM :: (forall s. KeyM s a) -> a
\end{code}
\caption{The Key monad interface}
\label{interface}
\end{figure}

The interface of our proposed extension, called the ``Key Monad'', is show in Figure \ref{interface}. The interface features two abstract types (types of which the constructors are not available to the user): |Key| and |KeyM|. The Key Monad gives the user the power to create a new, unique, |Key s| via |newKey|. The only operation that is supported on the type |Key| is |testEquality|, which checks if two given keys are the same, and if they are a ``proof'' is returned that the types assocatied with the names are the \emph{same} types. Such a  proof of the equality of type |a| and |b| is given as the GADT |a :~: b|. The |KeyM| computation can be run with |runKeyM|, which requires that the type argument |s| is polymorphic, ensuring that |Key|s cannot escape the |KeyM| computation. 


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


\subsection{Using keys for heterogenous maps}

To implement the |ST| monad using the |Key| monad, we also need a \emph{heterogeneous map}: a datastructure that that maps keys to values of the type corresponding to the key. The heterogenous maps we develop in this subsection can be extended with  \emph{without changing} the \emph{type} of the map. We can implement such maps as follows\footnote{For simplicity, this is a rather inefficient implementation, but a more efficient implementation using |IntMap|s can be given if we use a function |hashKey :: Key s a -> Int|}:
\begin{code}
newtype KeyMap s = Km [Box s]

empty :: KeyMap s
empty = Km []

insert :: Key s a -> a -> KeyMap s -> KeyMap s
insert k v (Km l) = Lock k v : l

lookup :: Key s a -> KeyMap s -> Maybe a
lookup k (Km [])       = Nothing
lookup k (Km (h : t))  = 
  maybe (lookup k (Km t)) (unlock k)
\end{code}

\subsection{Implementing the |ST| monad}

Armed with our newly obtained |KeyMap|s, we can (inefficiently) implement the |ST| monad as follows. The implementation of |STRef|s is simply as an alias for |Key|s:
\begin{code}
type STRef s a = Key s a
\end{code}
We can now use the Key monad to create new keys, and use a |KeyMap| to represent the current state of all created |STRef|s.
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
readSTRef r = (\env -> env ! r) <$> get

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef k v = modify (insert k v)
\end{code}
Finally, the implementation of |runST| simply runs the monadic computation contained in the |ST| type:
\begin{code}
runST :: (forall s. ST s a) -> a
runST (Km m) = runKeyM (evalStateT empty m)
\end{code}

\subsection{Difference with the ST monad}

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
Hence, another way to think of this paper is that we signal that the above function is \emph{safe}, and that this allows us to do things which we could not do before.

\subsection{Key monad laws}

The behavior of the Key monad is more precisely specified by the monad laws and the Key monad laws shown in Figure \ref{laws}. The |sameKey| and |distinctKey| laws describe the behavior of |testEquality|. The notation |E[x]| in these laws, means the expression |x| in an arbitrary expression context |E[]| (such that the free variables of |x| are not bound by |E[]|). 

\begin{figure}
\hspace{-0.7cm}
\begin{tabular}{ r  c  l r}
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    E[testEquality k k]
\end{code}
\end{minipage}& |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    E[Just Refl]
\end{code}
\end{minipage}& (|sameKey|) \\[-0.2cm]
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    E[testEquality k l]
\end{code}
\end{minipage}&  |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    E[Nothing]
\end{code}
\end{minipage}& (|distinctKey|) \\[-0.2cm] \begin{minipage}{0.22\columnwidth}
\begin{code}
do  x <- m 
    y <- n
    f x y
\end{code}
\end{minipage}
 &  |=| & \hspace{-0.5cm}\begin{minipage}{0.2\columnwidth}
\begin{code}
do  y <- n
    x <- m
    f x y
\end{code}
\end{minipage}
& (|commutative|) \\[-0.2cm]
\begin{minipage}{0.15\columnwidth} \begin{code}m >> n\end{code}\end{minipage} & |=| & \hspace{-0.5cm}\begin{minipage}{0.1\columnwidth} \begin{code} n\end{code} \end{minipage} & (|purity|)  \\[-0.2cm]
\begin{minipage}{0.35\columnwidth} \begin{code} runKey (return x) \end{code}\end{minipage}& |=| &\hspace{-0.55cm} \begin{minipage}{0.1\columnwidth} \begin{code}x\end{code} \end{minipage} & (|runReturn|) \\[-0.2cm]
\begin{minipage}{0.35\columnwidth} \begin{code} runKey (f <$> m)\end{code} \end{minipage}  & |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth} \begin{code}f (runKey m)\end{code}\end{minipage} & (|runF|) \\[-0.15cm]
\multicolumn{3}{c}{(if |m :: forall s. KeyM s a|)} & 
\end{tabular}
\caption{Key monad laws}
\label{laws}
\end{figure}

The |commutative| law states that the Key monad is a commutative monad: the order of actions does not matter. The |purity| law might be a bit suprising: it states that doing some Key computation and then throwing away the result is the same as not doing anything at all! The reason for this is that the only property of each key is that it is distinct from all other keys: making keys and then throwing them away has no (observable) effect on the rest of the computation.

The last two laws, |runReturn| and |runF|,  state how we can get the values out of a |KeyM| computation with |runKey|. The |runF| law states that we can lazily get the results of a (potentially) infinite |KeyM| computation. The side condition that |m| has type |forall s. KeyM s a| (for some type |a|) rules out wrong specialization of the law, such as:  
\begin{code}
runKey (f <$> newKey) = f (runKey newKey)
\end{code}
This specialization does \emph{not} hold because, the left hand side type-checks, but the right hand side does not: the ``s'' would escape. 



\section{Embedding Arrow notation}

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

The |Arrow| type class, recalled in Figure \ref{arrowsdef}, was introduced by Hughes\cite{arrows} as an interface that is like monads, but which allows for more static information about the constructed computations to be extracted. However, in contrast to monads, arrows do not directly allow intermediate values to be \emph{named}, instead expressions must be written in \emph{point-free style}. As an example, an arrow computation which feeds the same input to two arrows, and adds their outputs, can be expressed in point free style as follows:
\begin{code}
addA :: Arrow a => a x Int -> a x Int -> a x Int
addA f g =  arr (\x -> (x,x))  >>> first f >>> 
            second g           >>> arr (\(x,y) -> x + y)
  where  second x = flip >>> first x >>> flip
         flip     = arr (\(x,y) -> (y,x))
\end{code}
With monads, a similar computation could be written more clearly by naming intermediate values:
\begin{code}
addM :: Monad m =>  (x -> m Int) -> (x -> m Int) -> 
                    (x -> m Int)
addM f g = \z ->
    do  x <- f z
        y <- g z
        return (x + y)
\end{code}
To overcome this downside of arrows, Paterson's introduced arrow notation\cite{arrownot}. In this notation, the above arrow computation can be written as follows:
\begin{code}
addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = procb z -> do
   x <- f -< z
   y <- g -< z
   returnA -< x + y
\end{code}
Specialized compiler support is offered by the GHC, which desugars this notation into point free expressions. 

In this section, we show that with the Key monad, we can name intermediate values in arrow computations using \emph{regular} monadic do notation, without relying on specialized compiler support. The same arrow computation can be expressed using our \emph{embedded} arrow notation as follows: 
\begin{code}
addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = proc $ \z -> do
    x <- f -< z
    y <- g -< z
    return $ (+) <$> x <*> y
\end{code}
We use a function conviently called |proc| and use an infix function conviently called |(-<)|.

The difference between |do| notation and |proc| notation is that in |proc| notation, one cannot observe intermediate values to decide what to do next. For example, we \emph{cannot} do the following:
\begin{code}
ifArrow ::  a Int x -> a Int x -> a Int x
ifArrow t f = procb z -> do
   case z of
     0 -> t -< z
     _ -> f -< z
\end{code}
Allowing this kind of behavior would make it impossible to translate |proc| notation to arrows, because this is exactly the power that monads have but that arrows lack \cite{idiomarrmonad}. To mimic this restriction in our embedded arrow notation, our function |(-<)| has the following type:
\begin{code}
(-<) :: Arrow a => a x y -> Cage s x -> 
              ArrowSyn s (Cage s y)
\end{code}
Where |ArrowSyn| is the monad which we use to define our embedded arrow notation. The input and output of the arrow computations are enclosed in |Cage|s, which are named thusly because a value of type |Cage s x| does not allow observation of the value of the type |x| it ``contains''. The implementation of a |Cage| is as follows:
\begin{code}
newtype Cage s x = Cage { liberate :: KeyMap s -> x }
  deriving (Functor, Applicative)
\end{code}
Informally, a |Cage| ``contains'' a value of type |x|, but in reality it does not contain a value of type |x| at all: it is a function from a |KeyMap| to a value of type |x|. Hence we can we sure that we do not allow pattern matching on the result of an arrow computation, because the result is simply not available.

By using |(-<)| and the monad interface, we can construct the syntax for the arrow computation that we are expressing. Afterwards, we use the following function to convert the syntax to an arrow:
\begin{code}
proc ::  Arrow a => (forall s. Cage s x -> ArrowSyn a s y) 
         -> a x y
\end{code}

Internally, the |ArrowSyn| monad builds an arrow from environment to environment, and creates names (keys) for values in these environments using |KeyM|.
\begin{code}
newtype ArrowSyn a s x =
    AS (WriterT (EndoA a (KeyMap s)) (KeyMap s) x)
       deriving Monad
\end{code}
Where |EndoA a x| is an arrow from a type |x| to the same type:
\begin{code}
newtype EndoA a x = EndoA (a x x)
\end{code}
Such arrows form a monoid as follows:
\begin{code}
instance Arrow a => Monoid (EndoA a x) where
    mempty = EndoA (arr id)
    mappend (EndoA l) (EndoA r) = EndoA (l >>> r)
\end{code}
The standard writer monad transformer, |WriterT|, produces |mempty| for |return|, and composes the built values from from the left and right hand side of |>>=| using |mappend|, giving us precisely what we need for building arrows. 

The |KeyMap| in this construction functions as an \emph{enviroment}, each result of an arrow notation via |(-<)| has its own name (|Key|), and a |Cage| is an expression, i.e. a function from enviroment to value, which may lookup names in the enviroment. The |Key| monad and the |KeyMap| allow us to model \emph{hetrogenous} enviroments which can be extended \emph{without changing} the \emph{type} of the enviroment. This is exactly the extra power we need to define this translation. 



To define the operations |proc| and |(-<)|, we first define some auxiliary arrows for manipulating environments. 
We can easily convert a name (|Key|) to the expression (|Cage|) which consists of just that name:
\begin{code}
toCage :: Key s a -> Cage s a
toCage k = Cage (\env -> env ! k)
\end{code}
We can introduce an environment from a single value, when given a name (|Key|) for that value: 
\begin{code}
introEnv :: Arrow a => Key s x -> a x (HMap s)
introEnv k = arr (singleton k)
\end{code}
We also define an arrow to eliminate an environment, by interpreting an expression (|Cage|) using that environment:
\begin{code}
elimEnv ::  Cage s x -> a (HMap s) x
elimEnv c = arr (liberate c)
\end{code}
Next to introducing and eliminating environments, we also need to extend an environment and evaluate an expression while keeping the environment:
\begin{code}
extendEnv :: Arrow a =>  Key s x ->
                         a (x, HMap s) (HMap s)
extendEnv k = arr (uncurry (insert k))

withEnv :: Arrow a =>  Cage s x ->
                       a (HMap s) (x, HMap s)
withEnv c = dup >>> first (elimEnv c)
    where dup = arr (\x -> (x,x))
\end{code}

With these auxiliary arrows, we can define functions that convert back and forth between a regular arrow and an arrow from environment to environment. To implement |(-<)|, we need to convert an arrow to an arrow from environment to environment, for which we need an expression for the input to the arrow, and a name for the output of the arrow:
\begin{code}
toEnvA ::  Arrow a =>  
           Cage s x  -> Key s y   -> 
           a x y -> a (HMap s) (HMap s)
toEnvA inC outK a  =
   withEnv inC >>> first a >>> extendEnv outK
\end{code}
We first produce the input to the argument arrow, by interpreting the input expression using the input environment. We then execute the arguments arrow, and bind its output to the given name to obtain the output environment.

In the other direction, to implement |arrowize| we need to convert an arrow from environment to environment back to an arrow of type |x| to type |y|, for which we instead need the name of the input and an expression for the output:
\begin{code}
fromEnvA ::  Arrow a =>
             Key s x   -> Cage s y  ->
             a (HMap s) (HMap s) -> a x y
fromEnvA inK outC a  =
   introEnv inK >>> a >>> elimEnv outC
\end{code}
We first bind the input to the given name to obtain the input environment. We then transform this environment to the output environment by running the arrow from environment to environment. Finally, we interpret the output expression in the output environment to obtain the output.

The |(-<)| operation creates a name for the output and is given the input expression, which we use to convert the argument arrow using |toEnvA|: 
\begin{code}
(-<) :: Arrow a =>
        a x y ->
        (Cage s x -> ArrowSyn a s (Cage s y))
a -< inC = AS $
   do  outK <- lift newKey
       tell (EndoA $ toEnvA inC a outK)
       return (lookupVar outK)
\end{code}
Vice versa, the |proc| operation creates a name for the input and obtains the output expression, which we then uses to convert the obtained arrow from environment to environment using |fromEnvA|:
\begin{code}
proc ::  Arrow a =>
             (forall s. Cage s x -> ArrowSyn a s (Cage s y)) ->
             a x y
proc f = runKeyM $
      do  inK <- newKey
          let AS m = f (lookupVar inK)
          (outC, EndoA a) <- runWriterT m
          return (fromEnvA inK a outC)
\end{code} 

Notice that while with this construction we can construct arrows with a monadic interface, instead of proc notation, this does \emph{not} mean that arrows are a special case of monads. Arrows are a generalization of monads\cite{arrows}, but there is another generalization of monads called \emph{relative monads}, which is a generalization of both arrows and monads\cite{relmonad}. Because all operations in the monad |ArrowSyn|, namely |(-<)|, give value of type |Cage s a| instead of a ``bare'' value of type |a|, our construction is actually a relative monad, but we use a trick\cite{bjorn} to make this into a monad.




 

\section{Representations of variables in Syntax}

What else can we do with the Key monad? The Key monad allows us to associate types with ``names'' (|Key|s), and to see that if two names are the same, then their associated types are also the same. Use cases for this especially pop up when dealing with representations of syntax with binders, as we will show next.

\subsection{Typed names}

A straightforward way to represent the syntax of a programming language is to simply use strings or integers as names. For example, the untyped lambda calculus can be represented as follows:
\begin{code}
type Name  =  Int
data Exp   =  Var Name
           |  Lam Name Exp
           |  App Exp Exp
\end{code}
If we want to represent a \emph{typed} representation of the lambda calculus, then this approach does not work anymore. Consider the following GADT:
\begin{code}
data TExp a where
  Var :: Name -> TExp a
  Lam :: Name -> TExp b -> TExp (a -> b)
  App :: TExp (a -> b) -> TExp a -> TExp b
\end{code}
We cannot do much with this datatype: if we, for example, want to write an interpreter, then there is no type-safe way to represent the enviroment: we need to map strings to different types.

With the |Key| monad, we \emph{can} extend this simple naming approach to typed representations. Consider the following data type:
\begin{code}
data KExp s a where
  KVar :: Key s a -> KExp s a
  KLam :: Key s a -> KExp s b -> KExp s (a -> b)
  KApp :: KExp s (a -> b) -> KExp s a -> KExp s b
\end{code}
Because the names are now represented as keys, we can represented an enviroment as a |KeyMap|. We can even offer a Higher Order Abstract (HOAS) \cite{hoas} interface for constructing such terms by threading the key monad computation, which guarantees that all terms constructed with this interface are well-scoped:
\begin{code}
class Hoas f where 
  lam :: (f a -> f b)  -> f (a -> b)
  app :: f (a -> b)    -> (f a -> f b)

newtype HoasExp s a = 
  He { getExp :: KeyM s (KExp s a) }

instance Hoas (HoasExp s) where
  lam f = He $ do  k <- newKey 
                   b <- getExp (f (He (Var k)))
                   return (Lam k b)
  app f x = He $ App <$> getExp f <*> getExp x
\end{code}
For instance, the lambda term |(\x y -> x)| can now be constructed with:
\begin{code}
lam (\x -> lam (\y -> x))
\end{code}

\subsection{Translating well-scoped representations}

The datatype |KExp| does not ensure that any value of type |KExp| is well-scoped. As far as we know, there two are approaches to constructing datatypes for syntax which ensure that every value is well-scoped.  The first is Parametric Higher Order Abstract Syntax (HOAS)\cite{hoas, phoas, ags, graphs}, and the second is using typed de Bruijn indices\cite{nested}. However, there seems to be no way type-safe way to translate terms created with a PHoas term to typed de Bruijn indices, but the Key monad allows us to cross this chasm.
 
In Parametric HOAS, typed lambda terms are represented by the following data type:
\begin{code}
data Phoas v a where
  PVar :: v a -> Phoas v a
  PLam :: (v a -> Phoas v b) -> Phoas v (a -> b)
  PApp :: Phoas v (a -> b) -> Phoas v a -> PHoas b
\end{code}
The reading of the type parameter |v| is the type of \emph{variables}.
For example, the lambda term |(\x y -> x)| can be constructed as follows:
\begin{code}
phoasExample :: Phoas v (x -> y -> x)
phoasExample = PLam (\x -> PLam (\y -> x))
\end{code}
The attractive thing of Parametric HOAS is that we use Haskell binding to construct syntax, and that terms of type |(forall v. Phoas v a)| are always well-scoped\cite{phoas}.

The second way to ensure well-scopedness is to use typed de Bruijn indices. We present our own modern variant of this technique using Data Kinds and GADTs, but the idea is essentially the same as presented by Bird and Paterson \cite{nested} . Typed de Bruijn indices can represented as follows:
\begin{code}
data Index l a where
  HHead  :: Index (h : t) h
  HTail  :: Index t x -> Index (h : t) x
\end{code}
Here |l| is a type-level list representing the types in the enviroment, and an |Index l a| is a de Bruijn index in such an enviroment, of type |a|. We can use this insight to represent lambda terms as follows:
\begin{code}
data Bruijn l a where
  BVar  :: Index l a -> Bruijn l a
  BLam  :: Bruijn (a : l) b -> Bruijn l (a -> b)
  BApp  :: Bruijn l (a -> b) -> Bruijn l a -> Bruijn l b
\end{code}
A closed term of type |a| has type |Bruijn [] a|.


The types |(forall v. PHoas v a)| and |(Bruijn [] a)| both represent well-scoped typed lambda terms (and |undefined|), and translating from the latter to the former is straightforward. However, there seems to be no way to translate the former to the latter, without using extensions such as the |Key| monad. In other words there seems to be no function of type:
\begin{code}
phoasToBruijn :: (forall v. PHoas v a) -> NSyn [] a
\end{code} 
This seems to be not only be impossible in Haskell without extensions, but in dependently typed languages without extensions as well. When using |PHoas| in \emph{Coq} to prove properties about programming languages, an small extension to the logic in the form of a special well-formedness axiom for the |PHoas| datatype is needed to translate PHoas to de Bruijn indices\cite{phoas}. The |Key| monad is a general extension, which allows us to implement |phoasToBruijn|.

The well-scopedness of variables in a |Bruijn| value follows from the fact that the value is well-typed. With |PHoas|, the well-scopedness relies on the meta-level (i.e. not formalized through types) argument that no well-scoped values can be created by using the |PHoas| interface. The internal (i.e. formalized through types) well-scopedness of |Bruijn|, allows interpretations of syntax which seem to not be possible if we are using terms constructed with |PHoas|. As an example of this, consider translating lambda terms to \emph{cartesian closed category} combinators (the categorical version of the lambda calculus). This can be done if the lambda terms are given as |Bruijn| values, as demonstrated in Figure \ref{ccc}. Without the Key monad, there seem to be no way to do the same for terms constructed with the PHoas terms.

Our translation works by first translating |PHoas| to the |KExp| from the previous subsection, and then translating that to typed de bruijn indices. The first step in this translation is straightforwardly defined as follows: 
\begin{code}
phoasToKey ::  (forall v. PHoas v a) -> 
               (forall s. KeyM (KExp s a))
phoasToKey t = go t where
  go :: PHoas (Key s) a -> KeyM s (KLam s a)
  go (PVar x)    = return (KVar x)
  go (PLam f)    = do  v <- newKey
                       b <- go (f v)
                       return (KLam v b)
  go (PApp f x)  = KApp <$> go f <*> go x
\end{code}

We will now show how we can create a function of type:
\begin{code}
keyToBruijn :: KExp s a -> Bruijn [] a
\end{code}
Using this function, we can then implement |phoasToBruijn| as follows:
\begin{code}
phoasToBruijn :: (forall v. PHoas v x) -> Bruijn [] x
phoasToBruijn p = runKeyM 
   (keyToBruijn <$> phoasToKey p)
\end{code}
To implement the |keyToBruijn| function, we need a variant of the |Box| we saw previously:
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
newtype FKeyMap s f = FKm [FBox s f]
insert :: Key s a -> f a -> FKeyMap s f  -> FKeyMap s f
lookup :: Key s a -> FKeyMap s f -> Maybe (f a)
\end{code}
We also provide an instance for |PFunctor| for this datatype:
\begin{code}
instance PFunctor (FKeyMap s) where
  pfmap f (FKm m) = FKm (fmap (pfmap f) m)
\end{code}

We store the current ``enviroment'' as a |FKeyMap| mapping each |Key| to an |Index| in the current enviroment. When we enter a lambda-body, we need to extend the enviroment with a new name mapping to the de Bruijn index |HHead|, and add one lookup step to each other de Bruijn index currently in the |FKeyMap|. This is be done as follows:
\begin{code}
extend :: Key s h -> FKeyMap s (Index t) ->
            FKeyMap s (Index (h : t))
extend k m = insert k HHead (pfmap HTail m)
\end{code}
With this machinery in place, we can translate |KeyLam| to |NSyn| as follows:
\begin{code}
keyToBruijn :: KExp s a -> Bruijn [] a
keyToBruijn = go empty where
  go :: HFMap s (HIndex l) -> KExp s x -> Bruijn l x
  go e (KVar v)   = NVar (e ! v)
  go e (KLam k b) = NLam (go (extend k e) b)
  go e (KApp f x) = NApp (go e f) (go e x)
\end{code}
Notice that this translation may fail if we lookup a key in the enviroment which does not exists, but that this cannot happen if the |KExp| value is well-scoped, which is always the case when we translate |PHoas| to |KExp|.






\begin{figure}
\begin{code}
toClosed :: CCC c => Bruijn [] (x -> y) -> c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => NSyn l y -> TList l (c x) -> c x y
  go (BVar x)    e = findex e x
  go (BLam b)    e = curry $
                    go b (TCons snd (tmap (. fst) e))
  go (BApp f x)  e = uncurry (go f e) . prod id (go x e)

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

\section{Safety of the |Key| monad}

\subsection{Why adding extra types is not good enough}

The |Key| monad seems to be a perfectly safe thing, but it seems that it is not expressible in Haskell directly. It \emph{is} however, possible to implement a similar but weaker construction, which involves an extra type parameter that indicates the type of keys created in a computation. More precisely, this construction is not a monad, but an instance of the following type class, called the \emph{parametric effect monad} \cite{peff}:
\begin{code}
class Effect m where
   type Unit m :: k
   type Plus m :: k -> k -> k
   ireturn :: a -> m (Unit m) a
   (.>>=) :: m f a -> (a -> m g b) -> m (Plus m f g) b
\end{code}
The Key parametric effect monad then has the following interface:
\begin{code}
data KeyEff s l a 
instance Effect (KeyEff s) where
  type Unit (KeyEff s) = []
  type Plus (KeyEff s) = (++)
  ...

newKey :: KeyEff s [a] (Key s a)
runKeyEff :: (forall s. KeyEff s l a) -> a
\end{code}
The second type argument of |KeyEff| gives the list of the types of keys that are created within the |KeyEff| computation. Binding concatenates the two types of keys, and |newKey| is a |KeyEff| computation creating a single key.
The full implementation of this inteface can be found at ... 
While similar to the Key monad, this construction is \emph{less powerfull} than the regular key monad because the types of the keys which are going to be created must now be \emph{statically known}. All example use cases of the key monad in this paper rely on the fact that the type of the keys which are going to be created do not have to be statically know. For example, we cannot implement a translation from Parametric Hoas to de Bruijn indices with the Key parametric effect monad, because the type of the keys which will have to be created is precisely the information that a parametric HOAS representation lacks. 

 In the rest of this section, we argue informally for the safety of the |Key| monad and its implementation.
A straightforward implementation of the Key monad creates a new globally unique key for each key. For example, an implemenation using a plethora of unsafe extensions is as follows: 
\begin{code}
newtype KeyM  s a = KeyM {getKeyM :: IO a }
    deriving (Applicative, Functor)
newtype Key   s a = Key Unique

testEquality :: Key s a -> Key s b -> Maybe (a :~: b)
testEquality (Key i) (Key j) 
  | i == j     = Just (unsafeCoerce Refl)
  | otherwise  = Nothing

instance Monad (KeyM s) where
  return x = KeyM (return x)
  m >>= f  = KeyM $
    do x <- unsafeInterleaveIO (getKeyM m)
       f x
  m >> n   = n

newKey :: KeyM s (Key s a)
newKey = KeyM newUnique

runKeyM :: (forall s . KeyM s a) -> a
runKeyM (KeyM m) = unsafePerformIO m
\end{code}
This implementation has the disturbing feature that it uses \emph{three} functions whose names have |unsafe| as a prefix. A state monad implementation to provide unique numbers and only uses |unsafeCoerce| is also possible, but does not fulfill the law |m >> n = n|, which is why |unsafeInterleaveIO| is needed. Although it initially looks shady, we believe that this implementation is safe. But what do we mean precisely, when we say ``safe''?

\paragraph{Type safety}
The first safety property that we conjecture the Key monad has is \emph{type safety}: |testEquality| will never allow us to proof |a :~: b| for two \emph{distinct} types. The informal agument is that each Key has one type associated with it, and a unique number, and hence if the numbers are the same the types must also be the same. The assumption that each Key has \emph{one} type associated with it is broken if we have  a (non-bottom) value of type |forall a. Key s a| for some specific |s|. This hypothetical value can be used to construct |unsafeCoerce :: a -> b| because it is a unique key for \emph{any} type. The argument why no non-bottom value of this type can be created by using the key monad is that we can only create new keys with |newKey| and the type |forall s. KeyM (forall a. Key s a)| does not unify with the type of |newKey|, namely |forall s a. KeyM (Key s a)|. For the same reason, it is also not possible to get polymorphic references, i.e. references of type |(forall a. IORef a)| in Haskell.

\paragraph{Referential transparency} The second safety property that we are concerned with is \emph{referential transparency}: more specifically does the following still hold with the key monad extension:
\begin{code}
let x = y in (x,x) ==  (y,y) 
\end{code}
This is where the universal quantification in |runKeyM| comes into play, which is not needed for type safety (assuming globally unique keys). Operationally, the expressions |let x = runKeyM m in (x,x)| and |(runKeyM m, runKeyM m)| are \emph{not} the same, the latter will produce twice the amount of new keys that the former produces. However, because the argument of |runKeyM| is universally qualified, we can be sure that the keys created in the computation cannot escape. We will hence never be able to \emph{observe} wether the keys in two calls to |runKeyM| are distinct or different: programs which attempt to observe this are not type-correct. 

\paragraph{Abstraction safety} 
Abstraction safety is the property that we cannot break the abstraction barriers which are introduced through existential types. For example, if we have an existential type:
\begin{code}
data AbsBool where
  AbsBool ::  Eq a => a -> a -> (a -> b -> b -> b) 
              -> AbsBool
\end{code}
Which use in two ways:
\begin{code}
boolBool = 
  AbsBool True False (\c t f -> if c then t else f) 
boolInt  = 
  AbsBool  0 1        (\c t f -> if c == 0 then t else f)
\end{code}
If our language is abstraction safe, then it is impossible to observe any difference between |boolBool| and |boolInt|. This property is formalized by \emph{parametricity} (which also gives ``free'' theorems). A typical example of a primitive which is not abstraction safe (but is type-safe) is a primitive that allows us to check the equality of any two types:
\begin{code}
badTest :: a -> b -> Maybe (a :~: b)
\end{code}

The primitive |testEquality| is similar to the |badTest| primitive above, and indeed our operations on |Box| do allow us to ``break the abstraction barrier: if |unlock| succeeds, we have learned which type is hidden in the |Box|. However, finding out which type is hidden by an existential type is can not only be done with the Key monad, but also by the established Generalized Algebraic Datatypes extension of Haskell. For example, suppose we have the following type:
\begin{code}
data IsType a where
  IsBool  :: IsType Bool
  IsInt   :: IsType Int
  IsChar  :: IsType Char
\end{code}
We can then straightforwardly implement a variant of |testEquality|:
\begin{code}
testEquality :: IsType a -> IsType b -> Maybe (a :~: b)
testEquality IsBool  IsBool  = Just Refl
testEquality IsInt   IsInt   = Just Refl
testEquality IsChar  IsChar  = Just Refl
testEquality _       _       = Nothing
\end{code}
There are however formulations of parametricity which state more precisely exactly which abstraction barrier cannot be crossed\cite{type-safecast, bernardy_proofs_2012}, which still state that |boolBool| and |boolInt| are indistuingishable. The type |Key s|, for a specific |s|, can be thought of as a GADT:
\begin{code}
data Key s a where
  Key0 :: Key s Int
  Key1 :: Key s Bool
  ...
\end{code}
A tricky bit here is that since a |Key| computation might create an infinite number of keys, this hypothetical datatype might have an infinite number of constructors. We conjecture that there is a variant of parametricity for Haskell extended the Key monad in which, like with GADTs, states that |boolBool| and |boolInt| above are indistuingishable. 

\paragraph{Termination?}





Why no indexed monad? Staticily known types (and number of types), same as declaring |Key| GADT above!




\bibliographystyle{apalike}
\bibliography{refs}

\end{document}
