#include "env.h"

E_enventry E_VarEntry(Ty_ty ty){
	E_enventry var_entry=checked_malloc(sizeof(*var_entry));
	var_entry->kind=E_varEntry;
	var_entry->u.var.ty=ty;
	return var_entry;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result) {
	E_enventry fun_entry=checked_malloc(sizeof(*fun_entry));
	fun_entry->kind=E_funEntry;
	fun_entry->u.fun.formals=formals;
	fun_entry->u.fun.result=result;
	return fun_entry;
}

// type environment
S_table E_base_tenv(void) {
	S_table tenv=S_empty();
	S_enter(tenv, S_Symbol("int"), Ty_Int());
	S_enter(tenv, S_Symbol("string"), Ty_String());
	S_enter(tenv, S_Symbol("nil"), Ty_Nil()); // predefined function return type "nil"
	S_enter(tenv, S_Symbol("void"), Ty_Void()); // predefined function return type "void", error in 'test21.tig'
	return tenv;
}

// variable environment
S_table E_base_venv(void){
	S_table venv=S_empty();
	S_enter(venv, S_Symbol("print"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Void()));
	S_enter(venv, S_Symbol("flush"), E_FunEntry(NULL, Ty_Void()));
	S_enter(venv, S_Symbol("getchar"), E_FunEntry(NULL, Ty_String()));
	S_enter(venv, S_Symbol("ord"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(venv, S_Symbol("chr"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_String()));
	S_enter(venv, S_Symbol("size"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(venv, S_Symbol("substring"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String()));
	S_enter(venv, S_Symbol("concat"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
	S_enter(venv, S_Symbol("not"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_Int()));
	S_enter(venv, S_Symbol("exit"), E_FunEntry(Ty_TyList(Ty_Int(), NULL), Ty_Void()));
	return venv;
}
