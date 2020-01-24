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
               {e0}{{$e_0$}}2
               {e1}{{$e_1$}}2
               {e2}{{$e_2$}}2
               {ei}{{$e_i$}}2
    }
% These match in the middle of comments, which is unfortunate.
%               {pat}{{$p_i$}}2
%               {var}{{$x_0$}}2
%               {var1}{{$x_1$}}2
%               {var2}{{$x_2$}}2

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
\newcommand{\patList}[1]{\texttt{list}\;\brackets{#1}}
\newcommand{\patCons}[2]{\texttt{cons}\;\brackets{#1\;#2}}
\newcommand{\patEmpty}{\texttt{empty}}
\newcommand{\patAny}{\texttt{\_}}

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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
\end{code}

\begin{code}
module ScopeCheck
  ( ScopeCheck(..)
  , ScopeCheckT
  , runScopeCheckT
  , scopeCheckCoreF
  , Context(..)
  , newContext
  , scopeCheckRec
  , ScopeCheckError(..)
  ) where

import           Prelude hiding (head, tail)
import           Control.Monad (unless)
import qualified Control.Monad.Except as MTL
import qualified Control.Monad.Reader as MTL
import           Data.Foldable (for_)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T

import Core
import Phase

\end{code}

\subsection{The scope-checking monad}

In \klister{}, Scope checking is interleaved with macro expansion. As such, it
is written in the open recursive style, so that it can be suspended and subtasks
can be delayed.
\begin{code}

data ScopeCheckError
  = ScopeCheckErrorMessage Text
  | ScopeCheckInternalError Text
  deriving Show

-- | Laws:
--
-- * @forall v. bindVarIn v (use v) == pure ()@
class ScopeCheck f where
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
The pattern $\patList{x_1\;\ldots\;x_n}$ matches a vector of syntax objects of
length $n$:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patList{x_1\;\ldots\;x_n}}{\Gamma,x_1,\ldots,x_n}}
\end{equation*}
\begin{code}
    PatternList pairs -> bindVarsIn phase (map snd pairs)
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
The wildcard pattern $\patAny$ matches any syntax object, but doesn't provide a
 binding for it:
\begin{equation*}
  \frac{}{\pat{\Gamma}{\patAny}{\Gamma}}
\end{equation*}
\begin{code}
    PatternAny -> id
\end{code}

\subsection{Well-scoped expressions}

\begin{code}
scopeCheckCoreF ::
  (Applicative f, ScopeCheck f) =>
  (Phase -> a -> f ()) ->
  Phase ->
  CoreF a ->
  f ()
scopeCheckCoreF recur phase coreF =
  let inSameContext = flip for_ (recur phase)
  in
    case coreF of
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
        bindVarIn phase var (recur phase body)
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
          bindPatternIn phase pat (recur phase ei)
\end{code}
All other expressions bind no variables, so they are well-scoped when their
subtrees are:
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
      CoreLog e0 -> inSameContext [e0]
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
      CoreList (ScopedList elements pos) ->
        inSameContext (pos : elements)
\end{code}

\subsection{An instance of \texttt{ScopeCheck}}

The simplest instance of \texttt{ScopeCheck} simply records the in-scope
variables in a context and throws an exception when an unknown variable is
encountered.

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
newtype Context = Context { _getContext :: Map Phase (Set Var) }

newContext :: Context
newContext  = Context Map.empty

modifyContext :: Phase -> (Set Var -> Set Var) -> Context -> Context
modifyContext phase f (Context ctx) =
  Context $ Map.alter (Just . maybe Set.empty f) phase ctx

addToContext :: Phase -> Var -> Context -> Context
addToContext phase var = modifyContext phase (Set.insert var)

inContext :: Phase -> Var -> Context -> Bool
inContext phase var (Context ctx) =
  case Map.lookup phase ctx of
    Nothing -> False
    Just vars -> Set.member var vars

instance Semigroup Context where
  (Context ctxt1) <> (Context ctxt2) =
    Context $ Map.unionWith Set.union ctxt1 ctxt2

\end{code}

\subsubsection{The Monad}

\begin{code}
newtype ScopeCheckT m a =
  ScopeCheckT
    { _getScopeCheckT ::
       MTL.ReaderT Context (MTL.ExceptT ScopeCheckError m) a
    }
  deriving (Applicative, Functor, Monad)

deriving instance Monad m => MTL.MonadError ScopeCheckError (ScopeCheckT m)
deriving instance Monad m => MTL.MonadReader Context (ScopeCheckT m)

instance MTL.MonadTrans ScopeCheckT where
  lift = MTL.lift


-- TODO: is selective enough here?
instance Monad m => ScopeCheck (ScopeCheckT m) where
  use phase var = do
    ctx <- MTL.ask
    unless (inContext phase var ctx) $
      MTL.throwError (ScopeCheckErrorMessage $ "Variable not found:" <> T.pack (show var))

  bindVarIn phase var = MTL.local (addToContext phase var)

runScopeCheckT ::
  Monad m =>
  Context ->
  ScopeCheckT m a ->
  m (Either ScopeCheckError a)
runScopeCheckT ctxt (ScopeCheckT computation) =
  MTL.runExceptT $ MTL.runReaderT computation ctxt
\end{code}

\subsubsection{Recursion}

With the above instance in hand, we can write a straightforward recursive scope
checker.

\begin{code}
scopeCheckRec ::
  Monad m =>
  Phase ->
  Core ->
  ScopeCheckT m ()
scopeCheckRec ph = scopeCheckCoreF scopeCheckRec ph . unCore
\end{code}

\subsection{Another instance of \texttt{ScopeCheck}}

TODO(lb): Add an instance that collects all non-locally bound variables in a
 Writer

\end{document}
