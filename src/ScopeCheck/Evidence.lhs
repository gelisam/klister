\documentclass{article}
\title{Scope Checking Klister}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage[utf8]{inputenc}

% From https://wiki.haskell.org/Literate_programming
\usepackage{listings}
\lstloadlanguages{Haskell}
\lstnewenvironment{code}
    {\lstset{}%
      \csname lst@SetFirstLabel\endcsname}
    {\csname lst@SaveFirstLabel\endcsname}
    \lstset{
      language=Haskell,
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
               % for our purposes:
               {emptyContext}{{$\cdot$}}1
               {ctx}{{$\Gamma$}}1
               {var}{{$x_1$}}2
               {var1}{{$x_1$}}2
               {var2}{{$x_2$}}2
               {pat}{{$p_i$}}2
               {e0}{{$e_0$}}2
               {e1}{{$e_1$}}2
               {e2}{{$e_2$}}2
               {ei}{{$e_i$}}2
    }

% optionally automatically resized paired delimiters
\makeatletter % https://goo.gl/osSmHV
\DeclarePairedDelimiterX{\Braces}[1]{\{}{\}}{#1}
\DeclarePairedDelimiterX{\Brackets}[1]{[}{]}{#1}
\DeclarePairedDelimiterX{\Paren}[1]{\lparen}{\rparen}{#1}
\def\braces{\@ifstar{\Braces}{\Braces*}}
\def\brackets{\@ifstar{\Brackets}{\Brackets*}}
\def\paren{\@ifstar{\Paren}{\Paren*}}
\makeatother

\newcommand{\klister}{\textsc{Klister}}

% judgments
\newcommand{\ctx}[1]{#1\textbf{ ctx}}
\newcommand{\pat}[3]{#1 \vdash #2 \textbf{ pat} \leadsto #3}
\newcommand{\wellscoped}[2]{#1 \vdash #2\textbf{ well-scoped}}
\newcommand{\expandscope}[3]{#1 \vdash #2 \leadsto #3}

% patterns
\newcommand{\patIdent}[1]{\texttt{ident}\;#1}
\newcommand{\patVec}[1]{\texttt{vec}\;\brackets{#1}}
\newcommand{\patCons}[2]{\texttt{cons}\;\brackets{#1\;#2}}
\newcommand{\patEmpty}{\texttt{empty}}

% expressions
\newcommand{\eLam}[2]{\lambda #1.\;#2}
\newcommand{\eApp}[2]{#1\;#2}
\newcommand{\eAppII}[3]{\eApp{\eApp{#1}{#2}}{#3}}
\newcommand{\eAppIII}[4]{\eApp{\eApp{\eApp{#1}{#2}}{#3}}{#4}}
\newcommand{\ePure}[1]{\eApp{\texttt{pure}}{#1}}
\newcommand{\eBind}[2]{\eAppII{\texttt{bind}}{#1}{#2}}
\newcommand{\eError}[1]{\eApp{\texttt{error}}{#1}}
\newcommand{\eSend}[1]{\eApp{\texttt{send}}{#1}}
\newcommand{\eWait}[1]{\eApp{\texttt{wait}}{#1}}
% TODO: bound-identifier=?, free-identifier=?
\newcommand{\eSyntax}[1]{\eApp{\texttt{stx}}{#1}}
\newcommand{\eSyntaxCase}[2]{\texttt{syntax-case}\; #1\; #2}
\newcommand{\eIdentifier}[1]{#1}
\newcommand{\eTrue}{\texttt{true}}
\newcommand{\eFalse}{\texttt{false}}
\newcommand{\eSignal}{\texttt{signal}} % TODO: ???
\newcommand{\eIf}[3]{\eAppIII{\texttt{if}}{#1}{#2}{#3}}
\newcommand{\eIdent}[1]{\eApp{\texttt{ident-syntax}}{#1}}
\newcommand{\eEmpty}{\texttt{empty-syntax}}
\newcommand{\eCons}[2]{\eAppII{\texttt{cons-syntax}}{#1}{#2}}
\newcommand{\eVec}[1]{\eAppII{\texttt{vec-syntax}}{#1}}

% abbreviations for simple recursive cases
\newcommand{\wellScopedAlways}[1]{\frac{}{\wellscoped{\Gamma}{#1}}}
\newcommand{\wellScopedRecI}[1]{
  \frac{\wellscoped{\Gamma}{e}}{\wellscoped{\Gamma}{#1{e}}}
}
\newcommand{\wellScopedRecII}[1]{
  \frac{
    \wellscoped{\Gamma}{e_0}
    \hypspace \wellscoped{\Gamma}{e_1}
  }{\wellscoped{\Gamma}{#1{e_0}{e_1}}}
}
\newcommand{\wellScopedRecIII}[2]{
  \frac{
    \wellscoped{\Gamma}{e_0}
    \hypspace \wellscoped{\Gamma}{e_1}
    \hypspace \wellscoped{\Gamma}{e_2}
  }{\wellscoped{\Gamma}{#1{e_0}{e_1}{e_2}}}
}

\newcommand{\hypspace}{\qquad} % space between hypotheses
\setlength{\jot}{1em} % space between equations in multi-line envs
\begin{document}

\section{Scope checking}

\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
\end{code}

\begin{code}
module ScopeCheck.Evidence
  ( ScopeCheckTodo
  , scopeCheckCore
  ) where

import           Prelude hiding (head, tail)
import           Data.Foldable (for_)
import           Data.Set (Set)
import qualified Data.Set as Set

import Core
import SplitCore
import Module
import Phase
import Schedule

\end{code}

\subsection{The scope-checking monad}

In \klister{}, Scope checking is interleaved with macro expansion. As such, it
avoids a directly recursive style, instead scheduling further scope-checking
tasks along the way.
\begin{code}

data ScopeCheckError = ScopeCheckError ()
data ScopeCheckTodo a where
  TodoExpr :: SplitCorePtr -> ScopeCheckTodo (CoreF SplitCorePtr)
  TodoDecl :: DeclPtr -> ScopeCheckTodo (Decl DeclPtr SplitCorePtr)

-- | Laws:
--
-- * @forall v. bindVarIn v (use v) == pure ()@
class (Schedule f, Todo f ~ ScopeCheckTodo) => ScopeCheck f where
  -- | Record that this variable was used at this phase
  use :: Phase -> Var -> f ()
  -- | Extend the context with a variable in a subtask
  bindVarIn :: Phase -> Var -> f a -> f a


bindVarsIn :: (ScopeCheck f, Foldable t) => Phase -> t Var -> f a -> f a
bindVarsIn phase vars subtask =
  foldr (bindVarIn phase) subtask vars
\end{code}

\subsection{Patterns}

Patterns may add variables to the context.
\begin{code}
-- | Extend the context with variables captured in a pattern
bindPatternIn :: ScopeCheck f => Phase -> Pattern -> f a -> f a
bindPatternIn phase =
  \case
\end{code}
The pattern $\patIdent{x}$ matches an
identifier $x$ and makes it available on the RHS of the match:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patIdent{x}}{\Gamma,x}}
\end{equation*}
\begin{code}
    PatternIdentifier _ var -> bindVarIn phase var
\end{code}
The pattern $\patVec{x_1\;\ldots\;x_n}$ matches a vector of syntax objects of
length $n$:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patVec{x_1\;\ldots\;x_n}}{\Gamma,x_1,\ldots,x_n}}
\end{equation*}
\begin{code}
    PatternVec pairs -> bindVarsIn phase (map snd pairs)
\end{code}
The pattern $\patCons{x}{y}$ matches a cons cell of syntax objects:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patCons{x}{y}}{\Gamma,x,y}}
\end{equation*}
\begin{code}
    PatternCons _ var1 _ var2 ->
      bindVarIn phase var1 . bindVarIn phase var2
\end{code}
The empty pattern $\patEmpty$ matches an empty list of syntax objects, and binds
no new variables in the context:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patEmpty}{\Gamma}}
\end{equation*}
\begin{code}
    PatternEmpty -> id
\end{code}

\subsection{Well-scoped expressions}

\begin{code}
scopeCheckCore :: (Applicative f, ScopeCheck f) => Phase -> Core -> f ()
scopeCheckCore phase core =
  let inSameContext = flip for_ (scopeCheckCore phase)
  in
    case unCore core of
\end{code}
Variables are well-scoped in environments that contain them:
\begin{equation*}
  \frac{x \in \Gamma}{\wellscoped{\Gamma}{\eIdentifier{x}}}
\end{equation*}
\begin{code}
      CoreVar var -> use phase var
\end{code}
% TODO(lb): Can lambdas bind variables from elsewhere in the context (not just the end)?
Lambda expressions extend the context with an additional variable:
\begin{equation*}
  \frac{\wellscoped{\Gamma,x}{e}}{\wellscoped{\Gamma}{\eLam{x}{e}}}
\end{equation*}
\begin{code}
      CoreLam _ident var body ->
        bindVarIn phase var (scopeCheckCore phase body)
\end{code}
A \texttt{syntax-case} expression is well-scoped in $\Gamma$ when the RHS of
each branch is well-scoped in $\Gamma$ extended with the variables bound
in the pattern in the LHS of that branch:
\begin{equation*}
  \frac{
  \wellscoped{\Gamma}{e_0}
  \hypspace \pat{\Gamma}{p_i}{\Gamma_i}
  \hypspace \wellscoped{\Gamma_i}{e_i}
  }{\wellscoped{\Gamma}{\eSyntaxCase{e_0}{\brackets{p_i\;e_i}}}}
\end{equation*}
\begin{code}
      CoreCase e0 cases ->
        for_ cases $ \(pat, ei) ->
          inSameContext [e0] *>
          bindPatternIn phase pat (scopeCheckCore phase ei)
\end{code}
All other expressions are well-scoped when their subtrees are:
\begin{gather*}
  \wellScopedRecII{\eApp} \\
  \wellScopedRecI{\ePure} \\
  \wellScopedRecII{\eBind} \\
  \wellScopedRecI{\eError} \\
  \wellScopedRecI{\eSend} \\
  \wellScopedRecI{\eWait} \\
  \wellScopedRecI{\eSyntax} \\
  \wellScopedAlways{\eTrue} \\
  \wellScopedAlways{\eFalse} \\
  \wellScopedAlways{\eSignal} \\
  % TODO: ident, empty, cons, vec, and a few others
  \wellScopedRecIII{\eIf} \\
\end{gather*}
\begin{code}
      CoreApp e0 e1 -> inSameContext [e0, e1]
      CorePure e0 -> inSameContext [e0]
      CoreBind e0 e1 -> inSameContext [e0, e1]
      CoreSyntaxError (SyntaxError _ e0) -> inSameContext [e0]
      CoreSendSignal e0 -> inSameContext [e0]
      CoreWaitSignal e0 -> inSameContext [e0]
      CoreIdentEq _howEq e0 e1 -> inSameContext [e0, e1]
      CoreSyntax _syntax -> pure () -- TODO: is this right?
      CoreIdentifier _ident -> pure () -- TODO: is this right?
      CoreSignal _signal -> pure ()
      CoreBool _bool -> pure ()
      CoreIf cond thenBranch elseBranch ->
        inSameContext [cond, thenBranch, elseBranch]
      CoreIdent (ScopedIdent ident pos) ->
        inSameContext [ident, pos]
      CoreEmpty (ScopedEmpty e0) ->
        inSameContext [e0]
      CoreCons (ScopedCons head tail pos) ->
        inSameContext [head, tail, pos]
      CoreVec (ScopedVec elements pos) ->
        inSameContext (pos : elements)
\end{code}

\subsection{An instance of \texttt{MonadScopeCheck}}

The simplest instance of \texttt{MonadScopeCheck} simply recurs on the scheduled
tasks.

\subsubsection{Well-formed contexts}

During scope checking, a context $\Gamma$ records the set of variables that are
in scope. Well-formed contexts are either empty ($\cdot$), or a context extended
with a variable.
\begin{gather*}
  \frac{}{\ctx{\cdot}} \\
  \frac{\ctx{\Gamma} \hypspace x\notin\Gamma}{\ctx{\Gamma , x}}
\end{gather*}
The remainder of rules presented here presuppose that all contexts are
well-formed.

In the implementation, contexts are implemented as sets, so they are always
well-formed.

\begin{code}
newtype Context = Context { getContext :: Set Var }

emptyContext :: Context
emptyContext = Context Set.empty

modifyContext :: (Set Var -> Set Var) -> Context -> Context
modifyContext f (Context ctx) = Context (f ctx)

addToContext :: Var -> Context -> Context
addToContext var = modifyContext (Set.insert var)

addManyToContext :: Foldable f => f Var -> Context -> Context
addManyToContext vars ctx = foldr addToContext ctx vars

inContext :: Var -> Context -> Bool
inContext var (Context ctx) = Set.member var ctx
\end{code}

\end{document}
