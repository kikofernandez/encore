-- Defines how things will be called in the CCode generated by CodeGen.hs
-- Provides mappings from class/method names to their C-name

module CodeGen.CCodeNames where

import qualified AST as A
import CCode.CCode
import Data.Char

-- each method is implemented as a function with a `this`
-- pointer. This is the name of that function
method_impl_name :: A.Type -> A.Name -> Id
method_impl_name clazz mname =
    (show clazz) ++ "_" ++ (show mname)

-- each class, in C, provides a dispatch function that dispatches
-- messages to the right method calls. This is the name of that
-- function.
class_dispatch_name :: A.Type -> Id
class_dispatch_name clazz = (show clazz) ++ "_dispatch"

class_message_type_name :: A.Type -> Id
class_message_type_name clazz = (show clazz) ++ "_message_type"

class_trace_fn_name :: A.Type -> Id
class_trace_fn_name clazz = show clazz ++ "_trace"

method_message_type_name :: A.Type -> A.Name -> Id
method_message_type_name clazz mname = "m_"++show clazz++"_"++show mname

-- for each method, there's a corresponding message, this is its name
method_msg_name :: A.Type -> A.Name -> Id
method_msg_name clazz mname = "MSG_"++show clazz++"_"++show mname

-- the name of the record type in which a class stores its state
data_rec_name :: A.Type -> Id
data_rec_name clazz = show clazz ++ "_data"

actor_rec_name :: A.Type -> Id
actor_rec_name clazz = show clazz ++ "_actor"

-- a pointer to a class' state
data_rec_ptr :: A.Type -> Id
data_rec_ptr = (++"*") . data_rec_name

pony_actor_t_Type :: A.Type -> CType
pony_actor_t_Type (A.Type ty) =
    embedCType $ if isLower $ head ty
                 then ty
                 else ty++"_actor_t*"