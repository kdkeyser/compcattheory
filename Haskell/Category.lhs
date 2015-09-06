\documentclass[a4paper,10pt]{article}
\usepackage{listings}
\usepackage{bussproofs}
\usepackage{amsthm}
\lstloadlanguages{Haskell}
\lstnewenvironment{code}
            {\lstset{}%
      \csname lst@SetFirstLabel\endcsname}
    {\csname lst@SaveFirstLabel\endcsname}
    \lstset{
      basicstyle=\small\ttfamily,
      flexiblecolumns=false,
      basewidth={0.5em,0.45em},
      literate={+}{{$+$}}1 {/}{{$/$}}1 {*}{{$*$}}1 {=}{{$=$}}1
               {>}{{$>$}}1 {<}{{$<$}}1 {\\}{{$\lambda$}}1
               {\\\\}{{\char`\\\char`\\}}1
               {->}{{$\rightarrow$}}2 {>=}{{$\geq$}}2 {<-}{{$\leftarrow$}}2
               {<=}{{$\leq$}}2 {=>}{{$\Rightarrow$}}2
               {\ .}{{$\circ$}}2 {\ .\ }{{$\circ$}}2
               {>>}{{>>}}2 {>>=}{{>>=}}2
               {|}{{$\mid$}}1
    }

\begin{document}
\section{Defining categories in Haskell}
\subsection{General Categories}

\begin{itemize}
\item We should insist on equality of objects and morphisms, they are needed for the axioms.
\end{itemize}

\begin{code}

module Category where
import qualified Data.Set as Set
import Control.Exception.Base(assert)

data Category object morphism =
  Category { source :: morphism -> object,
             target :: morphism -> object,
             identity :: object -> morphism,
             compose :: morphism -> morphism -> Maybe morphism }
\end{code}
The following properties have to hold

\begin{prooftree}
\AxiomC{$\omega : *\ \ \mu : *\ c : Category(\omega,\ \mu) \ o : \omega$}
\UnaryInfC{\lstinline|source c $ identity c o| $==$ \lstinline|o|}
\end{prooftree}

\begin{prooftree}
\AxiomC{$\omega : *\ \ \mu : *\ c : Category(\omega,\ \mu) \ o : \omega$}
\UnaryInfC{\lstinline|target c $ identity c o| $==$ \lstinline|o|}
\end{prooftree}

\begin{prooftree}
\AxiomC{$\omega : *\ \ \mu : *\ c : Category(\omega,\ \mu) \ m : \mu$}
\UnaryInfC{\lstinline|compose c (identity $ source c m)  m| $==$ \lstinline|m|}
\end{prooftree}

\begin{prooftree}
\AxiomC{$\omega : *\ \mu : *  c : Category(\omega,\ \mu) \ m : \mu$}
\UnaryInfC{\lstinline|compose c m (identity $ target m)| $==$  \lstinline|m|}
\end{prooftree}

\begin{prooftree}
\def\fCenter{\mbox{\ $\vdash$\ }}
\AxiomC{$\omega : *\ \mu : * \ c : Category(\omega,\ \mu)\  m1, m2 : \mu\ \fCenter\ $
\lstinline|target c m1| $==$ \lstinline|source c m2|  }
\UnaryInfC{\lstinline| isJust $ compose c m1 m2| $==$ \lstinline|True|}
\end{prooftree}

\begin{prooftree}
\AxiomC{$\omega : *\ \mu : * \ c : Category(\omega,\ \mu)  m1, m2, m3 : \mu$}
\UnaryInfC{\lstinline|compose c m1 $ compose c m2 m3|  $==$  \lstinline|compose c (compose c m1 m2) m3 |}
\end{prooftree}

\subsection{Category Of Sets}
\begin{code}

data SetMorphism element =
  SetMorphism { setmorphism_source :: Set.Set element,
                setmorphism_target :: Set.Set element,
                setmorphism_morphism :: element -> element
              }

setmorphism_compose :: Eq element => SetMorphism element ->
                       SetMorphism element ->
                       Maybe (SetMorphism element)
setmorphism_compose s1 s2 =
  if setmorphism_target s1 == setmorphism_source s2 then
    Just $  s1 { setmorphism_target = setmorphism_target s2,
                 setmorphism_morphism =
                   (setmorphism_morphism s1). (setmorphism_morphism s2)}
  else Nothing

setmorphism_identity :: Set.Set element -> SetMorphism element
setmorphism_identity set = SetMorphism { setmorphism_source = set,
                                         setmorphism_target = set,
                                         setmorphism_morphism = id }

finSet :: Eq object => Category (Set.Set object) (SetMorphism object)
finSet = Category { source = setmorphism_source,
                    target = setmorphism_target,
                    identity = setmorphism_identity,
                    compose = setmorphism_compose }


\end{code}

\begin{code}
empty_morphism :: Set.Set element => SetMorphism element
empty_morphism set = SetMorphism {
  setmorphism_source = Set.empty,
  setmorphism_target = set,
  setmorphism_morphism = error "nil set morphism called"
  }

singleton_morphism :: Ord element => element ->
                      element ->
                      Set.Set element ->
                      SetMorphism element
singleton_morphism e1 e2 s =
  assert (Set.member e2 s) SetMorphism { setmorphism_source = Set.singleton e1,
                                         setmorphism_target =s,
                                         setmorphism_morphism = const e2}

\end{code}
\begin{code}
data UnitObj = UnitObj
data UnitMor = UnitMor

unit_category :: Category UnitObj UnitMor
unit_category = Category { source = const UnitObj,
                           target = const UnitObj,
                           identity = const UnitMor,
                           compose = const $ const (Just UnitMor)
                         }

\end{code}

\begin{code}
data FFunctor object1 morphism1 object2 morphism2 = FFunctor {
  functor_domain :: Category object1 morphism1,
  functor_range :: Category object2 morphism2,
  functor_object_map :: object1 -> object2,
  functor_morphism_map :: morphism1 -> morphism2
  }

functor_compose :: FFunctor o1 m1 o2 m2 ->
                   FFunctor o2 m2 o3 m3 ->
                   FFunctor o1 m1 o3 m3
functor_compose f1 f2 =
  f1  { functor_range = functor_range f2,
        functor_object_map = (functor_object_map f2) . (functor_object_map f1),
        functor_morphism_map = (functor_morphism_map f2) . (functor_morphism_map f1)
      }

type Isomorphism object1 morphism1 object2 morphism2 =
  (FFunctor object1 morphism1 object2 morphism2,
   FFunctor object2 morphism2 object1 morphism1)

\end{code}

\begin{code}
identityFunctor :: Category object morphism ->
               FFunctor object morphism object morphism
identityFunctor cat = FFunctor {
  functor_domain = cat,
  functor_range = cat,
  functor_morphism_map = id,
  functor_object_map = id
  }

-- Why k??
k :: Category object morphism ->
     object ->
     FFunctor UnitObj UnitMor object morphism
k cat object = FFunctor {
  functor_domain = unit_category,
  functor_range = cat,
  functor_object_map = const object,
  functor_morphism_map = const $ identity cat $ object
  }

-- Why o??
o :: Category object morphism ->
     FFunctor object morphism UnitObj UnitMor
o cat = FFunctor {
  functor_domain = cat,
  functor_range = unit_category,
  functor_object_map = const UnitObj,
  functor_morphism_map = const UnitMor }

\end{code}

\begin{code}
dualCategory :: Category object morphism ->
                Category object morphism
dualCategory cat = cat {
  source = target cat,
  target = source cat,
  compose = flip $ compose cat
  }

dualFunctor :: FFunctor object1 morphism1 object2 morphism2 ->
               FFunctor object1 morphism1 object2 morphism2

dualFunctor functor =
  functor { functor_domain = dualCategory $ functor_domain functor,
            functor_range = dualCategory $ functor_range functor
          }

\end{code}
\end{document}

%% Local Variables: **
%% compile-command: "pdflatex Category.lhs && evince Category.pdf" **
%% End: **
