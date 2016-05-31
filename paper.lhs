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
%format :++: =  ":\!\!+\!\!\!+\!\!:"
%format `Sub` = "\subseteq"
%format forall = "\forall"
%format exists = "\exists"
%format . = ".\:"
%format >>> = "\mathbin{>\!\!\!>\!\!\!>}"
%format .>>= = "\cdot\!\!\!\bind"
%format .>> = "\cdot\!\!>\!\!\!>"
%format -< = "\prec"
%format >- = "\succ"
%format ~ = "\:\sim\:"
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
\title{The Key Monad:\\Type-Safe Unconstrained Dynamic Typing}
\authorinfo{Atze van der Ploeg, Koen Claessen, Pablo Buiras}{Chalmers University of Technology}
           {\{atze, koen, buiras\}@@chalmers.se}
\begin{document}
\maketitle

\newcommand{\atze}[1]{{\it Atze says: #1}}
\newcommand{\koen}[1]{{\it Koen says: #1}}
\newcommand{\pablo}[1]{{\it Pablo says: #1}}

\section*{Alternative titles}

The Key Monad: more general than the ST-monad, less constrained than dynamic types

The Key Monad: providing unconstrained dynamic typing since 2000.

Pimp your existential types using the Key Monad

\section{Introduction}

The |ST|-monad \cite{st-monad} in Haskell is an impressive feat of language design, but also a complicated beast. It provides and combines three separate features: (1) an abstraction for {\em global memory references} that can be efficiently written to and read from, (2) a mechanism for embedding computations involving these memory references in {\em pure computations}, and (3) a design that allows references in the same computation to be of {\em arbitrary, different types}, in a type-safe manner.

\begin{figure}[t]
\rule{\columnwidth}{0.4pt}
\begin{code}
type KeyM s a
type Key s a

instance Monad (KeyM s)
newKey        :: KeyM s (Key s a)
testEquality  :: Key s a -> Key s b -> Maybe (a :~: b)
runKeyM       :: (forall s. KeyM s a) -> a

data a :~: b where Refl :: a :~: a
\end{code}
\caption{The Key monad interface}
\label{fig:key-monad}
\end{figure}

In this paper, we attempt to provide a new abstraction in Haskell that only provides feature (3) above: the combination of references (which we call {\em keys}) of different, unconstrainted types in the same computation. The result is a small library called {\em the Key Monad}. The API is given in Fig.\ \ref{fig:key-monad}.

The Key Monad |KeyM| is basically a crippled version of the |ST|-monad: we can monadically create keys of type |Key s a| using the function |newKey|, but we cannot read or write values to these keys; in fact, keys do not carry any value at all. We can convert a computation in |KeyM| into a pure value by means of |runKeyM|, which requires the computation to be polymorphic in |s|, just like |runST| would.

The only new feature is the function |testEquality|, which compares two keys for equality. But the keys do not have to be of the same type! They just have to come from the same |KeyM| computation, indicated by the |s| argument. If two keys are not equal, the answer is |Nothing|. However, if two keys are found to be equal, {\em then their types should also be the same}, and the answer is |Just Refl|, where |Refl| is a constructor from the GADT |a :~: b| that functions as the ``proof'' that |a| and |b| are in fact the same type\footnote{It is actually possible to add |testEquality| to the standard interface of |STRef|s, which would provide much the same features in the ST-monad as the Key Monad would, apart from some laziness issues\atze{Which laziness issues? I don't think there are any.}\koen{Yes: the lazy ST-monad is not as lazy as the name supply implementation}. However, because of its simplicity, we think the Key Monad is interesting in its own right. See also \ref{sec:discussion}.}.

Why is the Key Monad interesting? There are two separate reasons.

First, decoupling the ability to combine different types into one computation from computations involving state, allows programmers to use the Key Monad in situations where the ST-monad would not have been suitable. In fact, the bulk of this paper presents examples of uses of the Key Monad that would have been impossible without |testEquality|.

Second, the Key Monad is simpler than the ST-monad, because it does not involve global references, or any updatable state at all. We would like to argue that therefore, the Key Monad is easier to understand than the ST-monad. Moreover, given the Key Monad, the ST-monad is actually implementable in plain Haskell, albeit less time and memory efficient than the original ST-monad (so missing feature (1) above, but still providing feature (2) and (3)). So one could argue that, if one had to choose, the Key Monad would be the more desirable Haskell extension to pick.

The second reason comes with a possibly unexpected twist.

After its introduction in 1994, several papers have claimed to establish the correctness, fully or partially, of the ST-monad in Haskell \cite{...}. By correctness we mean three things: (a) type safety (programs using the ST-monad are still type safe), (b) referential transparency (programs using the ST-monad are still referentially transparent), and (c) abstraction safety (programs using the ST-monad still obey the parametricity theorem). It came as a complete surprise to the authors that {\em none of the papers we came across in our literature study actually establishes the correctness of the ST-monad in Haskell!}

So, there is a third reason for studying the Key Monad: A correctness proof for the Key Monad could be much simpler than a correctness proof for the ST-monad. The existence of such a proof would conceivably lead to a correctness proof of the ST-monad as well; in fact this is the route that we would currently recommend for anyone trying to prove the ST-monad correct.

This paper does not provide a formal correctness proof of the Key Monad. Instead, we will argue that the correctness of the Key Monad is just as plausible as the correctness of the ST-monad. We hope that the reader will not hold it against us that we do not provide a correctness proof. Instead, we would like this paper to double as a call to arms, to find (ideally, mechanized) proofs of correctness of both the Key Monad and the ST-monad!

\section{The Key Monad}

The interface of the Key Monad (Fig.\ \ref{fig:key-monad}) features two abstract types (types of which the constructors are not available to the user): |Key| and |KeyM|. The Key Monad gives the user the power to create a new, unique value of type |Key s a| via |newKey|. The only operation that is supported on the type |Key| is |testEquality|, which checks if two given keys are the same, and if they are a ``proof'' is returned that the types assocatied with the names are the \emph{same} types. Such a  proof of the equality of type |a| and |b| is given as a value of the GADT |a :~: b|. The |KeyM| computation can be run with |runKeyM|, which requires that the type argument |s| is polymorphic, ensuring that |Key|s cannot escape the |KeyM| computation. 

\subsection{Unconstrained dynamic typing}

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

We can use the |Box|es above to create a kind of \emph{heterogeneous maps}: a datastructure that that maps keys to values of the type corresponding to the key. The interesting feature here is that the type of these heterogenous maps does not depend on the types of the values that are stored in it. We can implement such maps as follows\footnote{For simplicity, this is a rather inefficient implementation, but a more efficient implementation (using |IntMap|s) can be given if we use a function |hashKey :: Key s a -> Int|}:
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

Armed with our newly obtained |KeyMap|s, we can implement a monad with the same interface as the |ST| monad as follows. The implementation of |STRef|s is simply as an alias for |Key|s:
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
readSTRef r = (fromJust . lookup r) `fmap` get

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
If we had such a function, then the |Key| monad would be trivially implementable with the |ST| monad (and vice versa). It is straightforward to implement the above function using |unsafeCoerce|:
\begin{code}
testEquality :: STRef s a -> STRef s b -> Maybe (a :~: b)
testEquality x y
   | x == y     = Just (unsafeCoerce Refl)
   | otherwise  = Nothing
\end{code}
Hence, another way to think of this paper is that we claim that the above function is \emph{safe}, that this allows us to do things which we could not do before, and that we propose this as an extension of the |ST|-monad library.

It \emph{is} possible to implement a similar, but weaker, version of |testEquality| using only the standard |ST|-monad functions. If we represent keys of type |Key s a| as a pair of an identifier and an |STRef|s containing values of type |a|, then we can create a function that casts a value of type |a| to |b|, albeit monadically.
\begin{code}
data Key s a =
  Key  {  ident  :: STRef s ()
       ,  ref    :: STRef s a
       }

testEqualityM :: Key s a -> Key s b -> Maybe (a -> ST s b)
testEqualityM ka kb
  |  ident ka /= ident kb  = Nothing
  |  otherwise             = Just $ \x ->
       do  writeSTRef (ref ka) x
           readSTRef (ref kb)
\end{code} 
This implementation, although a bit brittle because it relies on strong invariants, makes use of the insight that if the two references are actually the same reference, then writing to one reference must trigger a result in the other.

\subsection{Key monad laws}

The behavior of the Key monad is more precisely specified by the monad laws and the Key monad laws shown in Figure \ref{laws}. The |sameKey| and |distinctKey| laws describe the behavior of |testEquality|. The notation |E[x]| in these laws, means the expression |x| in an arbitrary expression context |E[]| (such that the free variables of |x| are not bound by |E[]|). 

\begin{figure}
\hspace{-0.7cm}
\begin{tabular}{ r  c  l r}
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    f (testEquality k k)
\end{code}
\end{minipage}& |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    f (Just Refl)
\end{code}
\end{minipage}& (|sameKey|) \\[-0.2cm]
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    f (testEquality k l)
\end{code}
\end{minipage}&  |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    f Nothing
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
proc ::  Arrow a => 
         (forall s. Cage s x -> ArrowSyn a s (Cage s y)) 
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
introEnv :: Arrow a => Key s x -> a x (KeyMap s)
introEnv k = arr (singleton k)
\end{code}
We also define an arrow to eliminate an environment, by interpreting an expression (|Cage|) using that environment:
\begin{code}
elimEnv ::  Cage s x -> a (KeyMap s) x
elimEnv c = arr (liberate c)
\end{code}
Next to introducing and eliminating environments, we also need to extend an environment and evaluate an expression while keeping the environment:
\begin{code}
extendEnv :: Arrow a =>  Key s x ->
                         a (x, KeyMap s) (KeyMap s)
extendEnv k = arr (uncurry (insert k))

withEnv :: Arrow a =>  Cage s x ->
                       a (KeyMap s) (x, KeyMap s)
withEnv c = dup >>> first (elimEnv c)
    where dup = arr (\x -> (x,x))
\end{code}

With these auxiliary arrows, we can define functions that convert back and forth between a regular arrow and an arrow from environment to environment. To implement |(-<)|, we need to convert an arrow to an arrow from environment to environment, for which we need an expression for the input to the arrow, and a name for the output of the arrow:
\begin{code}
toEnvA ::  Arrow a =>  
           Cage s x  -> Key s y   -> 
           a x y -> a (KeyMap s) (KeyMap s)
toEnvA inC outK a  =
   withEnv inC >>> first a >>> extendEnv outK
\end{code}
We first produce the input to the argument arrow, by interpreting the input expression using the input environment. We then execute the arguments arrow, and bind its output to the given name to obtain the output environment.

In the other direction, to implement |proc| we need to convert an arrow from environment to environment back to an arrow of type |x| to type |y|, for which we instead need the name of the input and an expression for the output:
\begin{code}
fromEnvA ::  Arrow a =>
             Key s x   -> Cage s y  ->
             a (KeyMap s) (KeyMap s) -> a x y
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

Because all the operations in the |ArrowSyn| return a |Cage|, it not possible to observe the output of an arrow computation to decide what to do next. While we cannot decide what to do next based on the output of a computation of type |ArrowSyn s (Cage s x)|, we can, for example, decide what to next based on the outcome of a computation of type |ArrowSyn s Int|. This does not give our embedded arrow notation more power than regular arrow notation: the value of the integer cannot depend on the result of an arrow computation and hence must be the result of a pure computation. This essentially the same trick as described in Svenningsson and Svensson\cite{bjorn}.

While the above construction is a monad, it is also possible to make a simillar construction for arrows which is a \emph{relative monad}\cite{relmonad}. A relative monad is an instance of the following type class:
\begin{code}
class RelMonad m v where
  rreturn :: v x -> m x
  (.>>=)  :: m x -> (v x -> m y) -> m y
\end{code}
The only difference with the regular monad type class is that the values are now wrapped in a type constructor |v|. The laws are also the same. Relative monads are a generalization of monads, because each monad can be made a relative monad by setting |v| to |Id|. 
We can construct a similar construction as |ArrowSyn| as follows:
\begin{code}
data ArrowRm a s x = ArrowRm 
         (ArrowSyn a s (Cage s x))
instance RelMonad (ArrowRm a s) (Cage s) where ...
\end{code}

Altenkrich\cite{relmonad} shows that in category theory arrows are a special case of relative monads, but his construction is not a relative monad in Haskell. In particular his definition of bind does not allow us freely use bound values, instead it requires us to manually lift values into scope, in the same fashion as directly using de Bruijn indices. Our construction suggests that arrows are also a special case of relative monad in Haskell with the key monad, but a formal proof is outside the scope of this paper.

The \emph{Arrow Calculus}\cite{arrowcalc} describes a translation of a form of arrow syntax (not embedded in Haskell) to arrows which is very simillar to the construction presented here. Their calculus has five laws, three of which can be considered to be relative monad laws, which they use to prove the equational correspondance between their calculus and regular arrows. Due to the simillarity, their paper should provide a good starting point for anyone trying to prove the same for this construction.





 

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
  Var  :: Name -> TExp a
  Lam  :: Name -> TExp b -> TExp (a -> b)
  App  :: TExp (a -> b) -> TExp a -> TExp b
\end{code}
We cannot do much with this datatype: if we, for example, want to write an interpreter, then there is no type-safe way to represent the enviroment: we need to map names to values of different types, but there is no type-safe way to do so.

With the |Key| monad, we \emph{can} extend this simple naming approach to typed representations. Consider the following data type:
\begin{code}
data KExp s a where
  KVar  ::  Key s a -> KExp s a
  KLam  ::  Key s a -> KExp s b -> KExp s (a -> b)
  KApp  ::  KExp s (a -> b) -> KExp s a -> KExp s b
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
  PVar  :: v a -> Phoas v a
  PLam  :: (v a -> Phoas v b) -> Phoas v (a -> b)
  PApp  :: Phoas v (a -> b) -> Phoas v a -> PHoas b
\end{code}
The reading of the type parameter |v| is the type of \emph{variables}.
For example, the lambda term |(\x y -> x)| can be constructed as follows:
\begin{code}
phoasExample :: Phoas v (x -> y -> x)
phoasExample = PLam (\x -> PLam (\y -> x))
\end{code}
An attractive property of Parametric HOAS is that we use Haskell binding to construct syntax, and that terms of type |(forall v. Phoas v a)| are always well-scoped\cite{phoas}.

The second way to ensure well-scopedness is to use typed de Bruijn indices. We present our own modern variant of this technique using Data Kinds and GADTs, but the idea is essentially the same as presented by Bird and Paterson \cite{nested}. Our representation of typed de Bruijn indices is an index in a hetrogenous list. In Figure \ref{heteros} we show definitions for heterogenous lists and indicices in them. A typed de Bruijn index of type |Index l a| is an index for a variable of type |a| in an enviroment where the types of the variables are represented by the type level list |l|. We can use these indices to represent lambda terms as follows:
\begin{code}
data Bruijn l a where
  BVar  :: Index l a -> Bruijn l a
  BLam  :: Bruijn (a : l) b -> Bruijn l (a -> b)
  BApp  :: Bruijn l (a -> b) -> Bruijn l a -> Bruijn l b
\end{code}
A closed term of type |a| has type |Bruijn [] a|.

\begin{figure}
\begin{code}
data Index l a where
  Head  :: Index (h : t) h
  Tail  :: Index t x -> Index (h : t) x

data TList f l where
  TNil  :: TList f [] 
  (:::) :: f h -> TList f t -> TList f (h : t)

index :: TList f l -> Index l a -> f a
index (h ::: _) Head     = h
index (_ ::: t) (Tail i) = index t i

pfmapl :: (forall x. f x -> g x) -> TList f l -> TList g l
pfmapl f TNil      = TNil
pfmapl f (h ::: t) = f h ::: pfmapl f t
\end{code}
\caption{Heterogenous list and indexes in them.}
\label{heteros}
\end{figure}

The types |(forall v. PHoas v a)| and |(Bruijn [] a)| both represent well-scoped typed lambda terms (and |undefined|), and translating from the latter to the former is straightforward. However, there seems to be no way to translate the former to the latter, without using extensions such as the |Key| monad. In other words there seems to be no function of type:
\begin{code}
phoasToBruijn :: (forall v. PHoas v a) -> Bruijn [] a
\end{code} 
This seems to be not only be impossible in Haskell without extensions, but in dependently typed languages without extensions as well. When using |PHoas| in \emph{Coq} to prove properties about programming languages, an small extension to the logic in the form of a special well-scopedness axiom for the |PHoas| datatype is needed to translate PHoas to de Bruijn indices\cite{phoas}.

The well-scopedness of variables in a |Bruijn| value follows from the fact that the value is well-typed. With |PHoas|, the well-scopedness relies on the meta-level (i.e. not formalized through types) argument that no well-scoped values can be created by using the |PHoas| interface. The internal (i.e. formalized through types) well-scopedness of |Bruijn|, allows interpretations of syntax which seem to not be possible if we are using terms constructed with |PHoas|. As an example of this, consider translating lambda terms to \emph{cartesian closed category} combinators (the categorical version of the lambda calculus). This can be done if the lambda terms are given as |Bruijn| values, as demonstrated in Figure \ref{ccc}. Without the Key monad, there seem to be no way to do the same for terms constructed with the PHoas terms.

The |Key| monad allows us to implement |phoasToBruijn|. This translation works by first translating |PHoas| to the |KExp| from the previous subsection, and then translating that to typed de bruijn indices. The first step in this translation is straightforwardly defined as follows: 
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
pfmap :: (forall x. f x -> g x) -> p f -> p g
pfmap f (FLock k x) = FLock k (f x)
\end{code} We also need a variant of the |KeyMap|, where we store |FBox|es instead of regular boxes:
\begin{code}
newtype FKeyMap s f = FKm [FBox s f]
insert :: Key s a -> f a -> FKeyMap s f  -> FKeyMap s f
lookup :: Key s a -> FKeyMap s f -> Maybe (f a)
\end{code}
We also provide an instance for |PFunctor| for this datatype:
\begin{code}
pfmapkm :: (forall x. f x -> g x) -> 
           FKeyMap s f -> FKeyMap s g
pfmapkm f (FKm m) = FKm (fmap (pfmap f) m)
\end{code}

We store the current ``enviroment'' as a |FKeyMap| mapping each |Key| to an |Index| in the current enviroment. When we enter a lambda-body, we need to extend the enviroment with a new name mapping to the de Bruijn index |HHead|, and add one lookup step to each other de Bruijn index currently in the |FKeyMap|. This is be done as follows:
\begin{code}
extend :: Key s h -> FKeyMap s (Index t) ->
            FKeyMap s (Index (h : t))
extend k m = insert k HHead (pfmapkm HTail m)
\end{code}
With this machinery in place, we can translate |KExp| to |Bruijn| as follows:
\begin{code}
keyToBruijn :: KExp s a -> Bruijn [] a
keyToBruijn = go empty where
  go :: HFMap s (HIndex l) -> KExp s x -> Bruijn l x
  go e (KVar v)   = NVar (e ! v)
  go e (KLam k b) = NLam (go (extend k e) b)
  go e (KApp f x) = NApp (go e f) (go e x)
\end{code}

Note that |keyToBruijn| fails if the input |KExp| is ill-scoped. This will never happen when |keyToBruijn| is called from |phoasToBruijn| because |phoasToKey| will always give well-scoped values of type |KExp|. This relies on the meta-level argument that values of type |PHoas| are always well-scoped. We stress that hence the key monad extension \emph{cannot} serve as a replacement of well-scopedness axiom used in a dependently typed setting. 






\begin{figure}
\begin{code}
toClosed :: CCC c => Bruijn [] (x -> y) -> c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => Bruijn l y -> TList l (c x) -> c x y
  go (BVar x)    e = index e x
  go (BLam b)    e = 
    curry $ go b (snd ::: pfmapl (. fst) e)
  go (BApp f x)  e = uncurry (go f e) . prod id (go x e)

class Category c => CCC c where
    prod     :: c x a -> c x b -> c x (a,b)
    fst      :: c (a,b) a
    snd      :: c (a,b) b
    curry    :: c (a,b) x -> c a (b -> x)
    uncurry  :: c a (b -> x) -> c (a,b) x
\end{code}
\label{ccc}
\caption{Translating lambda terms to cartesian closed categories.}

\end{figure}

\section{Implementing the Key monad}

\atze{What do you guys think about this section?}

The |Key| monad seems to be a perfectly safe thing, but it seems that it is not expressible in Haskell directly. Why?

To try to answer this question, we first discuss an implementation of the |Key| monad in Haskell which uses |unsafeCoerce|. To explore how far we can get without |unsafeCoerce|, we then discuss a weaker construction, called the Key paramateric effect monad. We then explore the relation between the two, which gives another way of thinking about the implementation of the |Key| monad.

\subsection{Implementation using |unsafeCoerce|}

We can straightforwardly implement the |Key| monad by giving each |Key| a unique name. One could implement generating unique names using a state monad, but the |(purity)| key monad law (|m >> n == n)| would then not hold. Instead, we implement the |Key| monad using an splittable name supply, with the following interface:
\begin{code}
newNameSupply  :: NameSupply
split          ::  NameSupply -> 
                   (NameSupply , NameSupply)
supplyName     :: NameSupply -> Name
\end{code}
The implementation of the |Key| monad is as follows:
\begin{code}
data KeyM s a = 
  KeyM { getKeyM :: NameSupply -> a }
data Key s a   = Key Name

newKey :: KeyM s (Key s a)
newKey = KeyM $ \s -> Key (supplyName s)

instance Monad (KeyM s) where
  return x      = KeyM $ \_ -> x
  m >>= f       = KeyM $ \s ->
     let (sl,sr) = split s
     in getKeyM (f (getKeyM m sl)) sr

runKeyM :: (forall s. KeyM s a) -> a
runKeyM (KeyM f)  = f newNameSupply
\end{code}
The |testEquality| function uses |unsafeCoerce|:
\begin{code}
testEquality (Key l) (Key r) 
  | l == r     = Just (unsafeCoerce Refl)
  | otherwise  = Nothing
\end{code}
The informal argument why this use of |unsafeCoerce| is safe is that each |Key| has a unique name and a single type associated with it, and hence when two |Key|s are the same their types must also be the same. 

But how do we implement such a |NameSupply|? One implementation of the |NameSupply| uses paths in a binary tree:
\begin{code}
data TreePath = Start | Left TreePath | Right TreePath
\end{code}
When reading left-to-right, these paths are given in reverse order from the root: the path |Left (Right Start)| is a path to the left child of the right child of the root. A name is then a path to leaf in a tree, and a namesupply is a path to a subtree. To split a |NameSupply|, we convert a path to a node into a path to the two children of that node:
\begin{code}
type NameSupply  = TreePath
type Name        = TreePath
newNameSupply  = Start
split s        = (Left s, Right s)
supplyName     = id
\end{code}

A |KeyM| computation consisting of |>>=|,|return| and |newKey| can also be seen as a binary tree where binds are node, |newKey|s are leaves and |return|s are empty subtrees. The |Name| associated with each key is the path to the |newKey| that created it, in the tree that corresponds to the |KeyM| computation. For example, the |Key| resulting from the |newKey| in the expression:
\begin{code}
runKeyM $ (m >> newKey) >>= f
\end{code}
will get the name |Right (Left Start)|.

\subsection{The key indexed monad}

While the |Key| monad is not expressible in Haskell without |unsafeCoerce|, it \emph{is} possible to implement a similar but \emph{weaker} construction. In this subsection, we show the implementation of this weaker construction, called the |Key| indexed monad,  and discuss its difference with the Key monad. 

Our weaker construction has the following interface:
\begin{code}
testEquality  ::  Key s a -> Key s b -> Maybe (a :~: b)

newKeyIm        ::  KeyIm s (Single a) (Key s a)

rreturn        ::  a -> KeyIm Empty s a
(.>>=)        ::  KeyIm s l a -> (a -> KeyIm s r b) 
                  -> KeyIm s (l :++: r) b

runKeyIm      :: (forall s. KeyIm s l a) -> a
\end{code}
This can be made an instance of the \emph{parametric effect monad} type class\cite{peff}.We can think of the second type argument to |KeyIm| as a type level list, where |Empty| is the empty list, |Single a| is a singleton list containing |a|, and |:++:| is concatenation.

While similar to the Key monad, this construction is \emph{less powerfull} than the regular key monad because the types of the keys which are going to be created must now be \emph{statically known}. All example use cases of the key monad in this paper rely on the fact that the type of the keys which are going to be created do not have to be statically know. For example, we cannot implement a translation from parametric Hoas to de Bruijn indices with |KeyIm|, because the type of the keys which will have to be created is precisely the information that a parametric HOAS representation lacks. 

A crucial insight is that is needed for this implemenation, is that it \emph{is} possible to implement to compare two indices in a heterogenous list, and produce a proof that their types are equal if their values are equal. This is can be done as follows:
\begin{code}
testEquality :: Index l a -> Index l b -> Maybe (a :~: b)
testEquality Head      Head      = Just Refl
testEquality (Tail l)  (Tail r)  = testEquality l r
testEquality _         _         = Nothing
\end{code}

We can employ the same insight to construct |testEquality| function for other datatypes. Instead of indexes in a heterogenous list, in our indexed |Key| monad, we use \emph{paths in a hetrogenous tree}. To introduce this datatype, we need to be able to construct type-level trees, for which we use the following datatype as a data-kind:
\begin{code}
data Tree a = Empty | Single a | Tree a :++: Tree a
\end{code}
With this datatype, we can construct types of kind |Tree| |*| such as:
\begin{code}
Single Int :++: (Single Bool :++: Single String)
\end{code}
We can now adapt the datatype |TreePath| to provide paths in type-level trees instead of value-level trees, in a similar fashion to how |Index| is an index in a type-level list instead of a value-level list:
\begin{code}
data TTreePath p w where
  Start   :: TTreePath w w
  Left    :: TTreePath (l :++: r) w -> TTreePath l w
  Right   :: TTreePath (l :++: r) w -> TTreePath r w
\end{code}
A value of type |TTreePath p w| is a path to the subtree |p| in the type-level tree |w|. For example, a path to |Single Bool| in the tree |Single Int :++: (Single Bool :++: Single String)| is |Left (Right Start)|.

We can now construct a |testEquality|-like function of the following type:
\begin{code}
samePath ::  TTreePath p w -> TTreePath p' w 
             -> Maybe (p :~: p')
\end{code}
The implementation of this function is a bit more involved than for |Index|, but is unsuprising:
\begin{code}
samePath Start      Start      = Just Refl
samePath (Left l)   (Left r)   = weakenL  <$> samePath l r
samePath (Right l)  (Right r)  = weakenR  <$> samePath l r
samePath _          _          = Nothing where 
  weakenL :: ((l :++: r) :~: (l' :++: r')) -> l :~: l'
  weakenL x = case x of Refl -> Refl

  weakenR :: ((l :++: r) :~: (l' :++: r')) -> r :~: r'
  weakenR x = case x of Refl -> Refl
\end{code}
By using this function and defining |data Key s a = Key (Name s a)|, we can implement |testEquality| \emph{without} |unsafeCoerce|.

With this machinery, we can implement a \emph{typed} name supply:
\begin{code}
type TNameSupply l s = TTreePath l s
type TName s a = TTreePath (Single a) s
\end{code}
A typed name supply of type |TNameSupply l s| gives unique names for the types in the subtree |l| which can be tested for equality with all unique names which are created in the context |s|. The implementation of the name supply function are completely analogous to their untyped counterparts: 
\begin{code}
newTNameSupply :: TNameSupply s s
newTNameSupply = Start

tsplit ::  TNameSupply (l :++: r) s 
           -> (TNameSupply l s, TNameSupply r s)
tsplit t = (Left t, Right t)

supplyTName :: TNameSupply (Leaf a) s -> TName s a
supplyTName = id
\end{code}

Using these type named supplies, the implementation of the key indexed monad is:
\begin{code}
data KeyIm s l a = KeyIm (TNameSupply l s -> a)
\end{code}
The implementation of the function |rreturn|, |.>>=|, |newKeyIm| and |runKeyIm| are 
\emph{exactly the same as their the regular |Key| monad counterparts}, using typed name supplies instead of regular name supplies.

Note that in the implementation |runKeyIm| now uses the type universally quantified type variable to |s| to unifiy |s| with |l|. This ``closes the context'', stating that the context is precisely the types which are created in the computation. In contrast, in |runKeyM| the type variable was not given an interpretation.


\subsection{Relation between implementations}

If we ignore the types that are involved, the implementations of the key monad and the key parametric effect monad are exactly the same. This suggests another implementation of the key monad, by hiding the extra type of |KeyIm|:
\begin{code}
data KeyM s a where
  KeyM :: KeyIm s p a -> KeyM s a
\end{code}
For presentational purposes we denote this type by |exists p. KeyIm s p a|, which is not valid (GHC) Haskell. While this allows us to provide type-safe implementations of |testEquality|, |fmap|, |newKey| and |return|, things go awry for |join| (or |>>=|) and |runKeyM|, where we need |unsafeCoerce|.

For |join| we need a implementation of type:
\begin{code}
join ::  (exists p. KeyIm s p (exists q. KeyIm s q a)) -> 
         exists r. KeyIm s r a
\end{code}
Expanding the definition of |KeyIm|, the type of the \emph{argument} we have is:
\begin{code}
exists p. TNameSupply p s -> exists q. TNameSupply q s -> a
\end{code} 
However, to use the implementation of |join| of |KeyIm|, we need the argument to be of type:
\begin{code}
exists p q. TNameSupply p s ->  TNameSupply q s -> a
\end{code}
These two types are \emph{not} equivalent: the latter implies the former, but not the other way around. However, in this situation we know more about the possible argument values than the types suggest. We know that |Key| is an abstract type for the user, who only has access to |testEquality|, not the constructors of |Key|. Hence the user-supplied argument function cannot distinguish between different value of the type |TNameSupply p s|. For example, the values |Left Start| and |Left (Left Start)| are indistinguisable for the argument function: they are only used to create unique names, and compare them, not to observe their exact value.   

For this reason, the type that is bound to |q| is the same type for all values of |TNameSupply p s|. Hence, one could argue that it is safe to coerce the argument from the former type to the later type. However, when a computation creates an infinite number of keys, this will also lead to an \emph{infinite} type, the consequences of allowing such types in Haskell are unknown to us.

Another problem arises at |runKeyM|. We get the type:
\begin{code}
runKeyM :: (forall s. exists p. KeyIm s p a) -> a
\end{code}
But to use |runKeyIm| the type should be:
\begin{code}
runKeyM :: (exists p. forall s. KeyIm s p a) -> a
\end{code}
Again, these are \emph{not} equivalent: the latter implies the former, but not the other way around. In particular, in the former type the type which is bound to |p| may depend on |s|, which cannot happen in the latter type.

 If the types of all keys which are created do not mention |s|, we do not for example create a key of type |Key s (Key s a)|, then one could argue that coercing the computation from the former to the latter is perfectly safe. However, if we create a key where the type does mention |s| then gives rises to \emph{cyclic} types , for example |s ~ (Key s Int) :++: t|. The consequences of allowing cyclic types in Haskell are unknown to us. In the next section, we show that using a key whose type mentions |s| allows us to implement |fix| without using recursion. 

While the above reasoning does not consitite a formal proof of the safety of the |Key| monad by any stretch of the imagination, it provides some evindence that the interpretation of the type parameter |s| to |KeyM| is that it is the type-level list of the types of keys that are going to be created.

\section{Safety of the |Key| monad}

\subsection{Why adding extra types is not good enough}



\begin{code}
newKey :: KeyEff s [a] (Key s a)
runKeyEff :: (forall s. KeyEff s l a) -> a
\end{code}



The second type argument of |KeyEff| gives the list of the types of keys that are created within the |KeyEff| computation. Binding concatenates the two types of keys, and |newKey| is a |KeyEff| computation creating a single key.






\paragraph{Type safety}
The first safety property that we conjecture the Key monad has is \emph{type safety}: |testEquality| will never allow us to proof |a :~: b| for two \emph{distinct} types. The informal agument is that each Key has one type associated with it, and a unique number, and hence if the numbers are the same the types must also be the same. The assumption that each Key has \emph{one} type associated with it is broken if we have  a (non-bottom) value of type |forall a. Key s a| for some specific |s|. This hypothetical value can be used to construct |unsafeCoerce :: a -> b| because it is a unique key for \emph{any} type. The argument why no non-bottom value of this type can be created by using the key monad is that we can only create new keys with |newKey| and the type |forall s. KeyM (forall a. Key s a)| does not unify with the type of |newKey|, namely |forall s a. KeyM (Key s a)|. For the same reason, it is also not possible to get polymorphic references, i.e. references of type |(forall a. IORef a)| in Haskell. Moreover, if the type of |runKeyM| is also crucial for type-safety. If its type was |KeyM s a -> a| instead of |(forall s. KeyM s a) -> a| we could create a polymorphic key with |runKeyM newKey :: forall a. Key s a|.

\paragraph{Referential transparency} The second safety property that we are concerned with is \emph{referential transparency}: more specifically does the following still hold with the key monad extension:
\begin{code}
let x = e in (x,x) ==  (e,e) 
\end{code}
For referential transparency, the universal quantification in |runKeyM| is key. Operationally, the expressions |let x = runKeyM m in (x,x)| and |(runKeyM m, runKeyM m)| are \emph{not} the same, the latter will produce twice the amount of new keys that the former produces. However, because the argument of |runKeyM| is universally qualified, we can be sure that the keys created in the computation cannot escape. We will hence never be able to \emph{observe} wether the keys in two calls to |runKeyM| are distinct or different: programs which attempt to observe this are not type-correct. 

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

\begin{code}
data D s a
  = Fun (Box s -> D s a)
  | Val a

apply :: Key s (D s a) -> D s a -> D s a -> D s a
apply k (Fun f) x = f (Hide k x)

unVal :: D s a -> a
unVal (Val x) = x

wrap :: Key s (D s a) -> (a -> a) -> D s a
wrap k f = Fun (Val . f . unVal . unHide k)

fix :: (a -> a) -> a
fix f = runKeyM (do k <- newKey
              let wf = Fun (\x -> apply k (wrap k f) (apply k (unlock k x) (unlock k x)))
              return (u (apply k wf wf)))
\end{code}


\bibliographystyle{apalike}
\bibliography{refs}

\end{document}
