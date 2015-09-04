\documentclass[a4paper,10pt]{article}
\usepackage{listings}
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
Remarks \\
\begin{itemize}
\item We should insist on equality of objects and morphisms... they are needed for the axioms.
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
                                         setmorphism_morphism = \_ -> e2}

\end{code}
\end{document}

%% Local Variables: **
%% compile-command: "pdflatex TheFirst.lhs && evince TheFirst.pdf" **
%% End: **
