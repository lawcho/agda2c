#! /usr/bin/env stack
-- stack script --optimize --resolver nightly-2023-04-28 --package Agda,containers,raw-strings-qq,transformers,text,zenc

-- Agda backend to C, in a single file
-- Writes output to stderr, info to stdout.

{-# LANGUAGE LambdaCase,OverloadedStrings,QuasiQuotes #-}
import Agda.Compiler.Backend
import Agda.Main (runAgda')
import Agda.Syntax.Internal (Term(..),Elim'(Apply))
import Agda.Syntax.Common (Arg(Arg),defaultArgInfo)
import Agda.Syntax.Literal (Literal(..))
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.Utils.Function (iterate')
import Agda.Utils.Monad (mapMaybeM, forMaybeM)
import Agda.Utils.Pretty
import Control.Monad ((<=<),(>=>))
import Control.Monad.Trans.Class (lift)
import Data.List (concat,elemIndices)
import Data.Functor ((<&>))
import Data.Text (Text)
import qualified Agda.Compiler.Treeless.Builtin as TT
import qualified Agda.Compiler.Treeless.EliminateDefaults as TT
import qualified Agda.Compiler.Treeless.EliminateLiteralPatterns as TT
import qualified Agda.Compiler.Treeless.GuardsToPrims as TT
import qualified Agda.Compiler.Treeless.NormalizeNames as TT
import qualified Data.Map.Strict as DM
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified System.IO as IO
import qualified Text.RawString.QQ as RSQ
import qualified Text.Encoding.Z as Zenc

main = runAgda' [Backend Backend'
-- Based off Agda hackage docs,
-- https://hackage.haskell.org/package/Agda-2.6.3/docs/Agda-Compiler-Backend.html
    {   backendName = "agda2c"
    ,   backendVersion = Nothing
    ,   options = ()
    ,   commandLineFlags = []
    ,   isEnabled = const True
    ,   scopeCheckingSuffices = False
    ,   mayEraseType = \_ -> return False
    ,   preCompile = \_ -> return ()
    ,   preModule = \_ _ _ _ -> return $ Recompile ()
    ,   compileDef = \_ _ _ -> return
    ,   postModule = \_ _ _ _ -> return
    ,   postCompile = \_ _ -> compile . concat . DM.elems
    }]

-- Compile all the definitions
compile :: [Definition] -> TCM ()
compile ds = do
    -- Compile the pure Agda code
    (qnames , cFunDefns) <- unzip <$> mapMaybeM compileDefinition ds
    -- Compile the FFI
    ffic_qnames <- scrapePragmas "C_FFI_COMPILER" ds  -- find the FFI compiler
    compiled_exposed <- mapM (runFFICompiler ffic_qnames) =<< scrapePragmas "C" ds  -- apply FFI compiler to {-# COMPILE C #-}-marked defintions
    compiled_raw_c <- mapM reduceToStringLit =<< scrapePragmas "RAW_C" ds  -- normalise {-# COMPILE RAW_C #-}-marked definitions directly
    -- Emit code
    emitLines "prelude imports" [preludeImports]
    emitLines "values of {-# COMPILE RAW_C #-}-taged strings" compiled_raw_c
    emitLines "declarations of compiled Agda identifiers" $ map ((<> ";") . qname2csig) qnames
    emitLines "prelude definitions" [preludeDefns]
    emitLines "definitions of compiled Agda identifiers" cFunDefns
    emitLines "compiled FFI" compiled_exposed

-- Print non-debug Text
emitLines :: Text -> [Text] -> TCM ()
emitLines tag lines = lift . Text.hPutStrLn IO.stderr . Text.unlines $ ["// Begin "<> tag] ++ lines ++ ["// End "<> tag]

-- Boilerplate code to insert at in the output
preludeImports, preludeDefns :: Text
preludeImports = [RSQ.r|
#if !defined(λ)
#define λ(var, body) ({VarType* var = mkVar(); lam(var, body);})
#endif
#include"bubs.h"
#include<assert.h>
#include<stdbool.h>
#include<stdint.h>
#include<limits.h>
|]
preludeDefns = [RSQ.r|
// Begin definitions of misc. helper functions
// Replacement for the from_prim(whnf(t)) pattern,
// which works even when t is parentless
unsigned int from_prim_whnf(Term* t)
    {Term* tmp = lam(mkVar(), t);    // give t a parent to satisfy whnf()'s precondition
    unsigned int result = from_prim(whnf(t));
    collect(tmp);   // collect the temporary parent (and potentially t too)
    return result;}
// End definitions of misc. helper functions
// Begin definitions of run-time errors
Term* error_postulate_evaluated(void) {assert(false);}
Term* error_erased_evaluated(void) {assert(false);}
Term* error_sort_evaluated(void) {assert(false);}
Term* error_unreachable_term_evaluated(void) {assert(false);}
Term* error_metavariable_evaluated(void) {assert(false);}
// End definitions of run-time errors
// Begin defintions of unsupported treeless literals
// The op0 wrapper moves the crash from Term-construction-time to Term-reduction-time
Term* unsupported_LitWord64_op0(void) {assert(false);}
Term* unsupported_LitWord64(void) {return op0(unsupported_LitWord64_op0);}
Term* unsupported_LitFloat_op0(void) {assert(false);}
Term* unsupported_LitFloat(void) {return op0(unsupported_LitFloat_op0);}
Term* unsupported_LitString_op0(void) {assert(false);}
Term* unsupported_LitString(void) {return op0(unsupported_LitString_op0);}
Term* unsupported_LitChar_op0(void) {assert(false);}
Term* unsupported_LitChar(void) {return op0(unsupported_LitChar_op0);}
Term* unsupported_LitQName_op0(void) {assert(false);}
Term* unsupported_LitQName(void) {return op0(unsupported_LitQName_op0);}
Term* unsupported_LitMeta_op0(void) {assert(false);}
Term* unsupported_LitMeta(void) {return op0(unsupported_LitMeta_op0);}
// End defintions of unsupported treeless literals
// Begin defintions of unsupported source-level primitives
Term* |]<> raw2cname "Agda.Builtin.String.primStringUncons" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primStringToList" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primStringFromList" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primStringAppend" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primStringEquality" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primShowChar" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primShowString" <>[RSQ.r|(void) {assert(false);}
Term* |]<> raw2cname "Agda.Builtin.String.primShowNat" <>[RSQ.r|(void) {assert(false);}
// End defintions of unsupported source-level primitives
// Begin shim definitions for treeless primitives
Term* prim_PIf_op0(void)
    // Align Scott-encoding with if-then-else order by flipping args
    {return λ(b,λ(kt,λ(kf,app(app(var(b),var(kf)),var(kt)))));}
Term* prim_PAdd_op2(Term** i1, Term** i2)
    {return prim(from_prim_whnf(*i1) + from_prim_whnf(*i2));}
Term* prim_PAdd_op0(void)
    {return λ(i1, λ(i2, op2(prim_PAdd_op2,var(i1),var(i2))));}
Term* prim_PSub_op2(Term** i1, Term** i2)
    {return prim(from_prim_whnf(*i1) - from_prim_whnf(*i2));}
Term* prim_PSub_op0(void)
    {return λ(i1, λ(i2, op2(prim_PSub_op2,var(i1),var(i2))));}
Term* prim_PEqI_op2(Term** i1, Term** i2)
    {if (from_prim_whnf(*i1) == from_prim_whnf(*i2))
        {return op0(|]<> raw2cname "Agda.Builtin.Bool.Bool.true" <>[RSQ.r|);}
    else
        {return op0(|]<> raw2cname "Agda.Builtin.Bool.Bool.false" <>[RSQ.r|);}}
Term* prim_PEqI_op0(void)
    {return λ(i1, λ(i2, op2(prim_PEqI_op2,var(i1),var(i2))));}
Term* prim_PSeq_op2(Term** t1, Term** t2)
    {whnf(*t1); return *t2;}
Term* prim_PSeq_op0(void)
    {return λ(t1, λ(t2, op2(prim_PSeq_op2,var(t1),var(t2))));}
// End shim definitions for treeless primitives
// Begin marshalling function definitions
// Agda -> C
uint16_t marshall_a2c_uint16_t(Term* t)
  {return (uint16_t) (from_prim_whnf(
    app ( app ( op0(|]<> raw2cname "Foreign-C.Core.to-Nat" <>[RSQ.r|)
              , op0(|]<> raw2cname "Foreign-C.Core.Ret-Type.uint16" <>[RSQ.r|))
        , t)
    ));}
bool marshall_a2c_bool(Term* t)
  {return (bool) (from_prim_whnf(
    app ( app ( op0(|]<> raw2cname "Foreign-C.Core.to-Nat" <>[RSQ.r|)
              , op0(|]<> raw2cname "Foreign-C.Core.Ret-Type.bool" <>[RSQ.r|))
        , t)
    ));}
void marshall_a2c_void(Term* t)
  {return;}
// C -> Agda
Term* marshall_c2a_uint16_t(uint16_t x)
  {return
    app ( app ( op0(|]<> raw2cname "Foreign-C.Core.from-Nat" <>[RSQ.r|)
              , op0(|]<> raw2cname "Foreign-C.Core.Ret-Type.uint16" <>[RSQ.r|))
        , prim(x));}
Term* marshall_c2a_bool(bool x)
  {return
    app ( app ( op0(|]<> raw2cname "Foreign-C.Core.from-Nat" <>[RSQ.r|)
              , op0(|]<> raw2cname "Foreign-C.Core.Ret-Type.bool" <>[RSQ.r|))
        , prim(x));}
Term* marshall_c2a_void(void)
  {return
    app ( app ( op0(|]<> raw2cname "Foreign-C.Core.from-Nat" <>[RSQ.r|)
              , op0(|]<> raw2cname "Foreign-C.Core.Ret-Type.void" <>[RSQ.r|))
        , prim(0));}
// End marshalling function definitions
|]

-- Logging helpers
debugLog :: VerboseLevel -> Text -> TCM ()
debugLog p = reportSLn "debug" p . Text.unpack

-- Crash with an error when compiling a definition
error' :: QName -> Text -> a
error' qn msg = error $ "Compilation of "<> prettyShow qn <>" failed because "<> Text.unpack msg

-- Compile a single definition
type CFunDefn = Text
compileDefinition :: Definition -> TCM (Maybe (QName, CFunDefn))
compileDefinition d =
    if defNoCompilation d
    then skip 2 "it is marked NoCompilation"
    else case theDef d of
        (AxiomDefn _)      ->   -- postulates compile to code that fails at run-time
                wrap "op0(error_postulate_evaluated)"
        (Constructor {conData}) -> do -- constructors compile to their Scott-encoding
            conPos <- getConstructorPos qname . theDef <$> getConstInfo conData
            conNArgs <- length . filter not <$> getErasedConArgs qname
            wrap $ showTreeless $ scottEncodeCtr conNArgs conPos
        (FunctionDefn _)   ->   -- functions compile to the UTLC, via Treeless
                toTreeless LazyEvaluation qname
            >>= maybe (skip 2 "toTreeless returned Nothing")
            (   cleanTreeless
            >=> wrap . showTreeless)
        _-> skip 3 "it is not a postulate, constructor, or function"
    where
        qname = defName d
        skip p reason = do
            debugLog p $
                "Skipping definition for "<> Text.pack (prettyShow qname) <>" because " <> reason
            return Nothing
        wrap cexp = return $ Just (qname, qname2csig qname <> "{\n  return "<> cexp <>";\n}")

-- Search a list of definitions for those which have a {-# COMPILE X #-} pragma
-- Throws an error for duplicate or junk-filled pragmas
scrapePragmas :: Text -> [Definition] -> TCM [QName]
scrapePragmas x ds = forMaybeM ds $ \d ->
    let qname = defName d in
    case defCompilerPragmas (Text.unpack x) d of
        [] -> return Nothing -- the defintion has no {-# COMPILE X #-} pragmas
        (_:_:_) -> error' qname $ "it has multiple {-# COMPILE "<> x <>" #-} pragmas"
        [CompilerPragma _ (_:_)] -> error' qname $ "it has pragma {-# COMPILE "<> x <>" #-} with non-empty text"
        [CompilerPragma _ []] -> return $ Just qname

-- Invoke the (pure Agda) FFI compiler on an identifier
runFFICompiler :: [QName] -> QName -> TCM Text
runFFICompiler [] qname = error' qname
    $ "it is marked with a {-# COMPILE C #-} pragma,"
    <>"but there is no {-# COMPILE C_FFI_COMPILER #-} marked defintion to process it!"
runFFICompiler (_:_:_) qname = error' qname
    $ "it is marked with a {-# COMPILE C #-} pragma,"
    <>"but there are multiple {-# COMPILE C_FFI_COMPILER #-} marked defintions to process it!"
runFFICompiler [ffi_compiler_qname] qname = do
    let term = Def ffi_compiler_qname $ map (Apply . Arg defaultArgInfo)
                [   (Lit . LitString . Text.pack . prettyShow) qname
                ,   (Lit . LitString . qname2cname) qname
                ,   Def qname []]
    infer term  -- fail gracefully if d is of wrong type in {-# COMPILE C d #-} pragma
    reduce term >>= \case
        Lit (LitString txt) -> return txt
        _ -> error' qname $
            "the FFI compiler failed to normalise it to a string literal at compile-time"

-- Normalize an identifier to a string literal
reduceToStringLit :: QName -> TCM Text
reduceToStringLit qname = reduce (Def qname []) >>= \case
    Lit (LitString txt) -> return txt
    _ -> error' qname "it failed to reduce to a string literal at compile-time"

-- Calculate where a constructor occurs in its datatype definition or record definition
getConstructorPos :: QName -> Defn -> (Int,Int)
getConstructorPos qn (DatatypeDefn dd) =
    case elemIndices qn (_dataCons dd) of
        [i] -> (i , length $ _dataCons dd)
        _ -> error' qn "it does not occur exactly once in its datatype defintion"
getConstructorPos qn (RecordDefn _) = (0,1) -- records always have exactly one constructor
getConstructorPos qn _ = error' qn "it is a constructor definiton, but its parent definition is no a record or datatype."


-- Convert an Agda identifier to a C identifier
raw2cname :: Text -> CName
raw2cname = ("build_"<>) . Text.pack . Zenc.zEncodeString . Text.unpack

type CName = Text
qname2cname :: QName -> CName
qname2cname = raw2cname . Text.pack . prettyShow

-- Convert an Agda identifier to a C function signature
type CFunSig = Text
qname2csig :: QName -> CFunSig
qname2csig qn = "Term* " <> qname2cname qn <> "(void)"

-- Run transformation passes (provided by the Agda compiler library)
-- to fix up the Treeless IR
cleanTreeless :: TTerm -> TCM TTerm
cleanTreeless
    =   TT.normalizeNames   -- must be last, as per comment in NormalizeNames.hs
    <=< TT.eliminateCaseDefaults
    <=< TT.eliminateLiteralPatterns
    <=< (pure . TT.convertGuards) -- must be after translateBuiltins, as per comment in GuardsToPrims.hs
    <=< TT.translateBuiltins

-- Generate a Scott-encoding for an A-argument constructor occuring
-- after M other constructors, in a datatype with N constructors in total
-- i.e.     (λ a1 .. aA k1 .. kN -> kM a1 .. aA)
-- N.B. the generated TTerm used DeBruijn *indices*
scottEncodeCtr :: Int -> (Int,Int) -> TTerm
scottEncodeCtr a (m,n) =
    iterate' (a + n) TLam $
    TApp (TVar (n-m-1)) $ reverse $ map TVar [n .. n+a-1]

-- Render DeBruijn *index* m of n as a DeBruijn *level* -based C identifier
showDBI :: Int -> Int -> Text
showDBI m n = ("v"<>) . Text.pack . show $ n - m

-- Pretty-print a Term from Agda's Treeless IR,
-- to a (gcc) C expression that uses the BUBS library
type CExpr = Text
showTreeless :: TTerm -> CExpr
showTreeless = go 0 where  -- Extra parameter for on-the-fly DeBruijn index->level conversion
    go :: Int -> TTerm -> CExpr
    go n (TVar v) = "var("<> showDBI v n <>")"
    -- Printing of lambdas relies on GCC's "Statement Expression" C extension
    go n (TLam body) = "λ("<> showDBI 0 (n+1) <>", "<> go (n+1) body <>")"
    -- Treeless 'let' bindings are non-recursive, so can safely be de-sugared to application of a lambda-expression.
    go n (TLet head body) = go n (TApp (TLam body) [head])
    -- Top level identifiers are compiled to op0 nodes which expand their definitions on-demand
    go n (TDef qn) = "op0("<> qname2cname qn <>")"
    go n (TCon qn) = go n (TDef qn) -- in the case of constructors, the expansion is to the Scott encoding
    -- The BUBS library is untyped, so coercions are stripped
    go n (TCoerce t) = go n t
    -- The unit value compiles to the integer constant 0
    go n TUnit = "prim(0)"
    -- Function applications are n-ary in Treeless but 2-ary in BUBS, so the compiler unfolds them
    go n (TApp fun args) = foldl (\acc t -> "app("<> acc <>", "<> go n t <>")") (go n fun) args
    go n (TPrim p) = "op0(prim_"<> (Text.pack . show) p <>"_op0)"
    -- 'Non-runtime' terms compile to code that fails at run-time
    go n TErased = "op0(error_erased_evaluated)"
    go n TSort = "op0(error_sort_evaluated)"
    go n (TError TUnreachable) = "op0(error_unreachable_term_evaluated)"
    go n (TError (TMeta _)) = "op0(error_metavariable_evaluated)"
    -- Nat literals compile to boxed unsigned ints
    go n (TLit (LitNat i)) = "prim("<> (Text.pack . show) i <>")"
    -- Other literals are unsupported, so compile to terms that crash on evaluation
    go n (TLit (LitWord64 _)) = "unsupported_LitWord64()"
    go n (TLit (LitFloat _)) = "unsupported_LitFloat()"
    go n (TLit (LitString _)) = "unsupported_LitString()"
    go n (TLit (LitChar _)) = "unsupported_LitChar()"
    go n (TLit (LitQName _)) = "unsupported_LitQName()"
    go n (TLit (LitMeta _ _)) = "unsupported_LitMeta()"
    -- Case splits compile to application of the scrutinee to the (λ-wrapped) cases
    go n (TCase v (CaseInfo _ ct) _ alts) = case ct of
        CTData _ _ -> go n $ TApp (TVar v) $ alts <&> \case
            (TAGuard {}) -> error $ "Encountered a TAGuard alternative in showTreeless"
            (TALit {}) -> error $ "Encountered a TALit alternative in showTreeless"
            (TACon _ conArity rhs) -> iterate' conArity TLam rhs
        _ -> error "Encountered a non-data case split in showTreeless"
