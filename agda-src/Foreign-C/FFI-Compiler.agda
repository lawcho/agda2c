
-- Part of the compiler implementation

-- Generate wrapper C code that implements the Agda/C FFI
-- (using the BUBS library)

-- This module relies on details of the Foreign-C.Core interface,
-- the AST compiler, and the interface of the BUBS runtime library

module Foreign-C.FFI-Compiler where

-- Names of some top-level Agda identifiers, as they appear in the C output.
-- Design note (Lawrence May '23):
--  Alternatives include:
--    * Agda's 'quote' syntax (does not provide z-encoding)
--    * Passing names in from AST compiler (requires complex AST-building)
module Phony-Zenc where
  module Agda where
    module Builtin where
      module Unit where
        tt = "build_AgdaziBuiltinziUnitzitt"
      module Sigma where
        fst = "build_AgdaziBuiltinziSigmaziz3a3Uzifst"
        snd = "build_AgdaziBuiltinziSigmaziz3a3Uzisnd"
  module Foreign-C where
    module Core where
      function-body = "build_ForeignzmCziCoreziExposedzifunctionzmbody"
      fun-handle = "build_ForeignzmCziCoreziCmdzmccallzifunzmhandle"
      fun-args = "build_ForeignzmCziCoreziCmdzmccallzifunzmargs"
      op-code = "build_ForeignzmCziCoreziCmdziopzmcode"
      cmd-arg = "build_ForeignzmCziCoreziCmdzicmdzmarg"
      head = "build_ForeignzmCziCoreziCCSzihead"
      tail = "build_ForeignzmCziCoreziCCSzitail"

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Foreign-C.Core

module Misc-Utils where
  _++_ = primStringAppend
  infixr 20 _++_

  private variable A B : Set

  -- Like for, but where the the function can see the index
  for' : List A → (Nat → A → B) → List B
  for' l f = go 0 l where
      go : Nat → List _ → List _
      go _ [] = []
      go n (a ∷ as) = f n a ∷ go (1 + n) as

  length : List A → Nat
  length [] = 0
  length (_ ∷ l) = 1 + length l

  intersperse : String → List String → String
  intersperse _ [] = ""
  intersperse sep (s ∷ []) = s
  intersperse sep (s ∷ ss) = s ++ sep ++ intersperse sep ss

  unwords unlines : List String → String
  unwords = intersperse " "
  unlines = intersperse "\n"

  case_of_ : A → (A → B) → B
  case x of f = f x

open Misc-Utils

-- Debug print a C type, to agda syntax
-- (this is like a Haskell "Show" instance, used for error messages etc.)
show-Ret-Ty : Ret-Type → String
show-Ret-Ty uint16 = "uint16"
show-Ret-Ty bool = "bool"
show-Ret-Ty void = "void"

show-Arg-Ty : Arg-Type → String
show-Arg-Ty uint16 = "uint16"
show-Arg-Ty bool = "bool"

-- Pretty-Print a C type, to C
print-Ret-Ty : Ret-Type → String
print-Ret-Ty uint16 = "uint16_t"
print-Ret-Ty bool = "bool"
print-Ret-Ty void = "void"

print-Arg-Ty : Arg-Type → String
print-Arg-Ty uint16 = "uint16_t"
print-Arg-Ty bool = "bool"

show-list : {A : Set} → (A → String) → List A → String
show-list _ [] = "[]"
show-list f as = "(" ++ unwords (map (λ x → f x ++ " ∷") as) ++ " [])"

-- Debug print a C function signature, to agda syntax
-- (this is like a Haskell "Show" instance, used for error messages etc.)
show-sig : Sig → String
show-sig (sig ret-ty name arg-tys) =
  "sig " ++ show-Ret-Ty ret-ty ++ " \"" ++ name ++ "\" " ++ show-list show-Arg-Ty arg-tys

-- Pretty-Print a C function signature, to C
print-sig : Sig → String
print-sig (sig ret-ty name arg-tys) =
  print-Ret-Ty ret-ty ++ " " ++ name ++ " ("++ intersperse "," args ++ ")"
  where args = for' arg-tys λ n ty →
          print-Arg-Ty ty ++ " arg" ++ primShowNat n

-- Generate an Agda/C FFI implementation from an Exposed value.
compile-fun : String → String → Exposed → String
compile-fun agda-ident compiled-agda-ident exposed = "
// This C function was generated for the Exposed Agda identifier "++ agda-ident ++"
// In particular, the FFI compiler inspected the .own-signature and .imported-sigs fields.
// For reference, the values of these fields are:
//  "++ agda-ident ++" .own-signature = "++ show-sig own-signature ++"
//  "++ agda-ident ++" .imported-sigs = "++ show-list show-sig imported-sigs ++"
" ++ print-sig own-signature ++ "{
  Term* t = op0("++ compiled-agda-ident ++");
  t = app(op0("++ Phony-Zenc.Foreign-C.Core.function-body ++"),t);  // extract the .function-body field
  t = app(t, op0("++ Phony-Zenc.Agda.Builtin.Unit.tt ++")); // apply to {{tt : Ret-Handle ( "++ show-Ret-Ty (own-signature .ret-ty) ++" )}}
" ++ unlines (for' imported-sigs λ n s →
    "  t = app(t, prim("++ primShowNat n ++"));  // apply to {{ "++ primShowNat n ++" : Call-Handle ( "++ show-sig s ++" ) }}"
  )++
  unlines (for' (own-signature .arg-tys) λ an ty →
    "  t = app(t, " ++ (case ty of λ where
        uint16 → "marshall_c2a_uint16_t(arg"++ primShowNat an ++")"
        bool   → "marshall_c2a_bool(arg"++ primShowNat an ++")"
    ) ++");  // apply to C argument "++ primShowNat (suc an) ++" of "++ primShowNat (№-args own-signature) ++ ", with type ⟦ "++ show-Arg-Ty ty ++" ⟧"
  )++ "

  // t now encodes ("++ agda-ident ++" .function-body), fully aplied to all its args

  Term* stream = t;

  // REPL-style FFI loop
  while (true){

    // Decode FFI command ocode
    Term* head = app(op0("++ Phony-Zenc.Foreign-C.Core.head ++"),stream);
    Term* tail = app(op0("++ Phony-Zenc.Foreign-C.Core.tail ++"),stream);
    Term* head_op_code = app(op0("++ Phony-Zenc.Foreign-C.Core.op-code ++"),head);
    Term* head_cmd_arg = app(op0("++ Phony-Zenc.Foreign-C.Core.cmd-arg ++"),head);

    unsigned int opcode = marshall_a2c_uint16_t(head_op_code);
    // tail and head_cmd_arg point to parentless Terms, so cannot be invalidated by whnf(head_op_code)
    // head_op_code, head potentially invalidated by whnf(head_op_code)

    // What kind of command is this?
    switch (opcode) {
      case 0: { //ccall

        // Decode function number
        Term* fun_handle = app(op0("++ Phony-Zenc.Foreign-C.Core.fun-handle ++"), head_cmd_arg);
        Term* args = app(op0("++ Phony-Zenc.Foreign-C.Core.fun-args ++"), head_cmd_arg);

        unsigned int fun_num = marshall_a2c_uint16_t(fun_handle);
        // args points to a parentless Term, so cannot be invalidated by whnf(fun_handle)
        // fun_handle, head_cmd_arg potentially invalidated by whnf(fun_handle)

        // What function to call?
        switch (fun_num) {"++
        unlines (for' imported-sigs λ sn s → "
          // "++ show-sig s ++"
          case "++ primShowNat sn ++ ": {
            // Normalise & decode Agda args to FFI call
            // Note (Lawrence May'23):
            //  normalising the n-tuple from the outside in avoids a factor-of-n slowdown
            Term* args_head;
            Term* args_tail;

"++         unlines (for' (s .arg-tys) λ xn t → "
            // Extract agda argument "++ primShowNat (suc xn) ++" of "++ primShowNat (№-args s) ++", with type ⟦ "++ show-Arg-Ty t ++" ⟧
              args_head = app(op0("++ Phony-Zenc.Agda.Builtin.Sigma.fst ++"),args);
              args_tail = app(op0("++ Phony-Zenc.Agda.Builtin.Sigma.snd ++"),args);
              "++ print-Arg-Ty t ++" x"++ primShowNat xn ++" = marshall_a2c_"++ print-Arg-Ty t ++"(args_head);

              // args_tail points to a parentless Term, so cannot be invalidated by whnf(args_head)
              // args_head, args potentially invalidated by whnf(args_head)
              args = args_tail;"
              )++"

            // The entire args tuple has now been traversed

            // Call the C function & encode its result
            Term* result = "++ (let
              args = for' (s .arg-tys) λ xn _ → "
                x"++ primShowNat xn
              call = s .name ++ "("++ intersperse "," args ++")"
              wrapped = case s .ret-ty of λ where
                  void → "("++ call ++",
              marshall_c2a_void());"
                  t → "marshall_c2a("++ call ++");"
            in wrapped
            ) ++ "

            stream = app(tail,result);   // Replace stream with applied tail
            break;
          }")++"
          default: {
            assert(false);
          }
        }
        break;
      }
      default: {   // return
        assert(false); // TODO: implement function return
      }
    }
  }
}
"   where
  open Exposed exposed
  open Sig
  №-args = λ s → length (s .arg-tys)

-- Help the AST compiler discover the QName of this function
{-# COMPILE C_FFI_COMPILER compile-fun #-}
