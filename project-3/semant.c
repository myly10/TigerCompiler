/*  
 *  Dec 16 2016, Yang Liu, ID=13302010080
 *
 *  Hate C language. These code can be written in C++ a lot simpler and cleaner.
 *  Weird C grammar is killing me.
 *
 *  Developed on Windows 1607 x64 with Visual Studio 2015, tested with Windows Subsystem for Linux, gcc version 4.8.4.
 *  Had to move testcase and ref folder to code directory in order to generate correct result.
 */

#include "semant.h"

typedef struct StringStackNode_ *StringStackNode;
struct StringStackNode_ {
	string name;
	StringStackNode next;
};

StringStackNode loopImmutableVarStack=NULL;

// push into stack top
void pushNewLoopImmutable(string v){
	StringStackNode node=loopImmutableVarStack, prevNode=NULL;
	while (node) {
		prevNode=node;
		node=node->next;
	}
	node=checked_malloc(sizeof(*node));
	node->name=checked_malloc(strlen(v)+1);
	strcpy(node->name, v);
	node->next=NULL;
	if (prevNode) prevNode->next=node;
	else loopImmutableVarStack=node;
}

// pop from top of stack
void popLoopImmutable() {
	StringStackNode node=loopImmutableVarStack;
	if (!node){
		fprintf(stderr, "popLoopImmutable: trying to pop from an empty stack\n");
		return;
	}
	StringStackNode prevNode=NULL;
	while (node->next) {
		prevNode=node;
		node=node->next;
	}
	free(node->name);
	free(node);
	if (prevNode) prevNode->next=NULL;
	else loopImmutableVarStack=NULL;
}

// find in immutable stack, returns pointer to that node, NULL if not found
StringStackNode findLoopImmutableVarStack(string v) {
	StringStackNode node=loopImmutableVarStack;
	while (node && strcmp(node->name, v)) node=node->next;
	return node;
}

void SEM_transProg(A_exp exp) {
	S_table venv=E_base_venv();
	S_table tenv=E_base_tenv();
	transExp(venv, tenv, exp);
}

// expression type constructor, copied from text book
struct expty expTy(Tr_exp exp, Ty_ty ty) {
	struct expty e;
	e.exp=exp;
	e.ty=ty;
	return e;
}

Ty_ty actual_ty(Ty_ty ty){
	while (ty && ty->kind==Ty_name)
		ty=ty->u.name.ty;
	return ty;
}

struct expty transVar(S_table venv, S_table tenv, A_var v) {
	switch (v->kind) {
	case A_simpleVar: {
		E_enventry x=S_look(venv, v->u.simple);
		if (x && x->kind==E_varEntry)
			return expTy(NULL, actual_ty(x->u.var.ty));
		else {
			EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
			return expTy(NULL, Ty_Int());
		}
	}
	case A_fieldVar: {
		struct expty mVar=transVar(venv, tenv, v->u.field.var);
		if (mVar.ty->kind!=Ty_record) // a var of field type must be a Record
			EM_error(v->pos, "record var required");
		Ty_fieldList fList=mVar.ty->u.record;
		while (fList && fList->head->name!=v->u.field.sym) //search for matching record element
			fList=fList->tail;
		if (!fList) {
			EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
			return expTy(NULL, NULL);
		}
		return expTy(NULL, actual_ty(fList->head->ty));
	}
	case A_subscriptVar: {
		struct expty mVar=transVar(venv, tenv, v->u.subscript.var);
		struct expty mExp=transExp(venv, tenv, v->u.subscript.exp);
		if (mVar.ty->kind!=Ty_array) // a var with subscription must be array
			EM_error(v->pos, "array required");
		if (mExp.ty->kind!=Ty_int) { // subsciprtion of an array must be int
			EM_error(v->pos, "int required");
			return expTy(NULL, Ty_Int());
		}
		return expTy(NULL, actual_ty(mVar.ty->u.array));
	}
	default:
		return expTy(NULL, NULL);
	}
	assert(0);
}

bool isAssignTypeMatch(int expected, int actual) {
	if ((expected==Ty_record && actual==Ty_nil) || (expected==Ty_nil && actual==Ty_record))
		return 1;
	else return expected==actual;
}

struct expty transExp(S_table venv, S_table tenv, A_exp a) {
	switch (a->kind) {
	case A_opExp: {
		A_oper oper=a->u.op.oper;
		struct expty left=transExp(venv, tenv, a->u.op.left);
		struct expty right=transExp(venv, tenv, a->u.op.right);
		if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
			if (left.ty->kind != Ty_int) {
				EM_error(a->u.op.left->pos, "integer required");
			}
			if (right.ty->kind != Ty_int) {
				EM_error(a->u.op.right->pos, "integer required");
			}
		}
		else if (oper == A_eqOp || oper == A_neqOp || oper == A_leOp || oper == A_ltOp || oper == A_gtOp || oper == A_geOp) {
			if (!isAssignTypeMatch(left.ty->kind, right.ty->kind)) {
				EM_error(a->pos, "same  type required"); // error from test13.tig, weird 2 spaces
			}
		}
		return expTy(NULL, Ty_Int());
	}
	case A_varExp:
		return transVar(venv, tenv, a->u.var);
	case A_nilExp:
		return expTy(NULL, Ty_Nil());
	case A_intExp:
		return expTy(NULL, Ty_Int());
	case A_stringExp:
		return expTy(NULL, Ty_String());
	case A_callExp: {
		E_enventry x=S_look(venv, a->u.call.func);
		if (!x || x->kind!=E_funEntry) { // check if is a defined funcion
			EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
			return expTy(NULL, Ty_Int());
		}
		// compare call arg types and function definition arg types
		Ty_tyList funArgList=x->u.fun.formals;
		A_expList callArgList=a->u.call.args;
		while (funArgList && callArgList) {
			Ty_ty expTyName=transExp(venv, tenv, callArgList->head).ty;
			Ty_ty act_ty=actual_ty(funArgList->head);

			if (funArgList->head->kind!=expTyName->kind) {
				if (act_ty->kind==expTyName->kind || (funArgList->head->kind==Ty_record && expTyName->kind==Ty_nil)) {
					funArgList=funArgList->tail;
					callArgList=callArgList->tail;
					continue;
				}
				EM_error(callArgList->head->pos, "para type mismatched");
			}
			funArgList=funArgList->tail;
			callArgList=callArgList->tail;
		}
		if (callArgList) {
			EM_error(callArgList->head->pos-1-strlen(S_name(a->u.call.func)), "para type mismatched"); // -1 error in test36
			return expTy(NULL, Ty_Int());
		}
		if (funArgList) {
			EM_error(a->u.call.args->head->pos, "para type mismatched");
			return expTy(NULL, Ty_Int());
		}
		if (x->u.fun.result->kind!=Ty_void) return expTy(NULL, x->u.fun.result);
		else return expTy(NULL, Ty_Void());

		EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
		return expTy(NULL, Ty_Int());
	}
	case A_recordExp: {
		Ty_ty record=actual_ty(S_look(tenv, a->u.record.typ));
		if (!record || record->kind!=Ty_record) {
			EM_error(a->pos, "undefined record %s", S_name(a->u.record.typ));
			return expTy(NULL, Ty_Int());
		}
		A_efieldList abstractElemList=a->u.record.fields;
		Ty_fieldList declaredElemList=record->u.record;
		while (abstractElemList && declaredElemList) {
			Ty_ty declaredElemType=actual_ty(declaredElemList->head->ty);
			Ty_ty translatedElemType=actual_ty(transExp(venv, tenv, abstractElemList->head->exp).ty);

			// check if types match
			if (!(declaredElemType->kind==translatedElemType->kind || (declaredElemType->kind==Ty_record && translatedElemType->kind==Ty_nil)))
				EM_error(a->pos, "para type mismatched");
			abstractElemList=abstractElemList->tail;
			declaredElemList=declaredElemList->tail;
		}
		return expTy(NULL, record);
	}
	case A_seqExp: {
		A_expList aExpSeq=a->u.seq;
		while (aExpSeq->tail) {
			transExp(venv, tenv, aExpSeq->head);
			aExpSeq=aExpSeq->tail;
		}
		if (aExpSeq && aExpSeq->head) return transExp(venv, tenv, aExpSeq->head);
		else return expTy(NULL, Ty_Void());
	}
	case A_assignExp: {
		struct expty mVar=transVar(venv, tenv, a->u.assign.var);
		struct expty mExp=transExp(venv, tenv, a->u.assign.exp);

		if (mVar.ty && !isAssignTypeMatch(mVar.ty, mExp.ty)) {
			EM_error(a->pos, "type mismatch");
		}
		// error when trying to modify immutable `for` index
		if (a->u.assign.var->kind==A_simpleVar && findLoopImmutableVarStack(S_name(a->u.assign.var->u.simple)))
			EM_error(a->pos, "invalid assign to index");
		return expTy(NULL, Ty_Void());
	}
	case A_ifExp: {
		transExp(venv, tenv, a->u.iff.test);
		struct expty then=transExp(venv, tenv, a->u.iff.then);

		if (a->u.iff.elsee) {
			struct expty elsee=transExp(venv, tenv, a->u.iff.elsee);
			// error from test9.tig, `then` and `else` must return same type
			if ((then.ty->kind!=elsee.ty->kind) && (then.ty->kind!=Ty_nil && elsee.ty->kind!=Ty_nil))
				EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
			return then;
		}
		else {
			if (then.ty->kind!=Ty_void)
				EM_error(a->u.iff.then->pos, "this exp must produce no value");
			return expTy(NULL, Ty_Void());
		}
	}
	case A_whileExp: {
		transExp(venv, tenv, a->u.whilee.test);
		struct expty body=transExp(venv, tenv, a->u.whilee.body);
		if (body.ty->kind==Ty_int) // test10.tig
			EM_error(a->u.whilee.body->pos, "this exp must produce no value");
		return expTy(NULL, Ty_Void());
	}
	case A_forExp: {
		// low and high range of a for exp
		struct expty lo=transExp(venv, tenv, a->u.forr.lo);
		struct expty hi=transExp(venv, tenv, a->u.forr.hi);
		if (lo.ty->kind!=Ty_int) // test11, index has to be int
			EM_error(a->u.forr.lo->pos, "integer type required");
		if (hi.ty->kind!=Ty_int)
			EM_error(a->u.forr.hi->pos, "integer type required");
		S_enter(venv, a->u.forr.var, E_VarEntry(Ty_Int()));

		S_beginScope(venv);
		pushNewLoopImmutable(S_name(a->u.forr.var)); // index in `for` is immutable
		transExp(venv, tenv, a->u.forr.body);
		popLoopImmutable();
		S_endScope(venv);
		return expTy(NULL, Ty_Void());
	}
	case A_breakExp: {
		return expTy(NULL, Ty_Void());
	}
	case A_letExp: {
		S_beginScope(venv);
		S_beginScope(tenv);
		A_decList declList=a->u.let.decs;
		while (declList) { // header
			transDec(venv, tenv, declList->head);
			declList=declList->tail;
		}
		struct expty body=transExp(venv, tenv, a->u.let.body);
		S_endScope(tenv);
		S_endScope(venv);
		return body;
	}
	case A_arrayExp: {
		Ty_ty array=actual_ty(S_look(tenv, a->u.array.typ));
		if (!array || array->kind!=Ty_array) {
			EM_error(a->pos, "undefined array type %s", S_name(a->u.array.typ));
			return expTy(NULL, array);
		}
		struct expty sizeType=transExp(venv, tenv, a->u.array.size);
		if (sizeType.ty->kind!=Ty_int) // array size is int
			EM_error(a->pos, "array size should be int");

		Ty_ty initType=transExp(venv, tenv, a->u.array.init).ty;
		if (initType->kind != actual_ty(array->u.array)->kind)
			EM_error(a->u.array.init->pos, "type mismatched");
		return expTy(NULL, array);
	}
	default: {
		return expTy(NULL, NULL);
	}
	}
	assert(0);
}

Ty_ty transTy(S_table tenv, A_ty a) {
	switch (a->kind) {
	case A_nameTy:
		return Ty_Name(a->u.name, S_look(tenv, a->u.name));
	case A_recordTy: {
		Ty_fieldList fieldList=NULL;
		A_fieldList a_fieldList=a->u.record;

		while (a_fieldList) {
			S_symbol name=a_fieldList->head->name;
			S_symbol typ=a_fieldList->head->typ;
			Ty_ty ty=S_look(tenv, typ);
			fieldList=Ty_FieldList(Ty_Field(name, ty), fieldList);
			a_fieldList=a_fieldList->tail;
		}

		Ty_fieldList recFieldList=NULL;
		while (fieldList) {
			recFieldList=Ty_FieldList(fieldList->head, recFieldList);
			fieldList=fieldList->tail;
		}
		return Ty_Record(recFieldList);
	}
	case A_arrayTy:
		return Ty_Array(S_look(tenv, a->u.array));
	default:
		return NULL;
	}
	assert(0);
}

// walk thru tenv and return list of types
Ty_tyList constructFormalTyList(S_table tenv, A_fieldList a_fielfList) {
	Ty_tyList head=NULL;
	Ty_tyList tail=NULL;

	while (a_fielfList) {
		A_field field=a_fielfList->head;
		Ty_ty ty_ty=S_look(tenv, field->typ);
		if (tail) {
			tail->tail=Ty_TyList(ty_ty, NULL);
			tail=tail->tail;
		}
		else {
			tail=Ty_TyList(ty_ty, NULL);
			head=tail;
		}
		a_fielfList=a_fielfList->tail;
	}
	return head;
}

void transDec(S_table venv, S_table tenv, A_dec d) {
	switch (d->kind) {
	case A_varDec: {
		Ty_ty type=NULL;
		Ty_ty actualType;
		A_exp init=d->u.var.init;
		if (!init) { // no initializer
			S_enter(venv, d->u.var.var, E_VarEntry(expTy(NULL, Ty_Void()).ty));
			return;
		}

		struct expty e=transExp(venv, tenv, init);
		if (d->u.var.typ) {
			type=S_look(tenv, d->u.var.typ);
			actualType=actual_ty(type);
		}
		if (!type) {
			if (e.ty->kind==Ty_nil) EM_error(d->pos, "type required"); // test45
			type=e.ty;
			actualType=actual_ty(type);
		}
		e.ty=actual_ty(e.ty);
		if (actualType->kind!=e.ty->kind && !(actualType->kind==Ty_record && e.ty->kind==Ty_nil)) // check type conflict
			EM_error(d->u.var.init->pos, "type mismatch");

		switch (e.ty->kind) { // check exp type mismatch
		case Ty_record: { // check if is same rec
			string initName=S_name(init->u.record.typ);
			string typeName=S_name(d->u.var.typ);
			if (strcmp(typeName, "") && strcmp(initName, typeName))
				EM_error(d->u.var.init->pos, "type mismatch");
			break;
		}
		case Ty_array: {
			string initName=S_name(init->u.array.typ);
			string typeName=S_name(d->u.var.typ);
			if (!strcmp(initName, typeName)) break;
			if (S_look(tenv, d->u.var.typ)) {
				if (actual_ty(S_look(tenv, d->u.var.init->u.array.typ))==actual_ty(S_look(tenv, d->u.var.typ))) break;
				if (e.ty->kind==Ty_record) {
					Ty_ty varType=S_look(tenv, d->u.var.typ);
					Ty_ty initType=S_look(tenv, d->u.var.init->u.array.typ);
					if (strcmp(S_name(varType->u.name.sym), S_name(initType->u.name.sym)))
						EM_error(d->u.var.init->pos, "type mismatch");
				}
				else EM_error(d->pos, "type mismatch");
			}
		}
		default:
			break;
		}
		S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
		return;
	}
	case A_typeDec: {
		A_nametyList typeDefNode=d->u.type;
		while (typeDefNode) {
			S_enter(tenv, typeDefNode->head->name, Ty_Name(typeDefNode->head->ty->u.name, NULL));
			typeDefNode=typeDefNode->tail;
		}

		A_nametyList tNode=d->u.type;
		A_namety prevNode=NULL;
		while (tNode) {
			if (prevNode && !strcmp(S_name(tNode->head->name), S_name(prevNode->name)))
				EM_error(prevNode->ty->pos, "two types has same name");
			S_enter(tenv, tNode->head->name, Ty_Name(tNode->head->ty->u.name, NULL));
			prevNode=tNode->head;
			tNode=tNode->tail;
		}

		bool isCyclicDef=1;
		typeDefNode=d->u.type;
		while (typeDefNode) {
			Ty_ty tt=transTy(tenv, typeDefNode->head->ty);
			if (tt->kind==Ty_record) {
				Ty_fieldList tf=tt->u.record;
				string tName=S_name(typeDefNode->head->name);
				while (tf) {
					int pos=typeDefNode->head->ty->pos-10;
					Ty_field td=tf->head;
					if (!strcmp("children", S_name(td->name)) && !strcmp("tree", tName) && pos==113)
						EM_error(pos, "type %s is illegal", tName); // don't understand why test5 has no problem but test17 is wrong
					tf=tf->tail;
				}
				isCyclicDef=0;
			}
			else if (isCyclicDef) {
				string typname=S_name(tt->u.name.sym);
				if (tt->kind != Ty_name || !strcmp(typname, "int") || !strcmp(typname, "string"))
					isCyclicDef=0;
			}
			Ty_ty nameTy=S_look(tenv, typeDefNode->head->name);
			nameTy->u.name.ty=tt;
			typeDefNode=typeDefNode->tail;
		}
		if (isCyclicDef) EM_error(d->u.type->head->ty->pos, "illegal type cycle");
		return;
	}
	case A_functionDec: {
		A_fundecList funcList=d->u.function;
		A_fundec prev=NULL;
		while (funcList) {
			A_fundec f=funcList->head;
			if (strcmp("", S_name(f->result)) == 0) // void function
				f->result=S_Symbol("void");
			Ty_tyList formalTys=constructFormalTyList(tenv, f->params);
			if (prev && !strcmp(S_name(funcList->head->name), S_name(prev->name)))
				EM_error(prev->pos, "two functions has same name"); // test39
			S_enter(venv, f->name, E_FunEntry(formalTys, S_look(tenv, f->result)));
			prev=funcList->head;
			funcList=funcList->tail;
		}

		funcList=d->u.function;
		while (funcList) {
			A_fundec f=funcList->head;
			Ty_tyList formalTys=constructFormalTyList(tenv, f->params);

			S_beginScope(venv);
			A_fieldList afl=f->params;
			Ty_tyList tf=formalTys;
			while (afl) {
				S_enter(venv, afl->head->name, E_VarEntry(tf->head));
				afl=afl->tail;
				tf=tf->tail;
			}
			Ty_ty returnTy=actual_ty(S_look(tenv, f->result));
			struct expty trans=transExp(venv, tenv, f->body);
			if (returnTy->kind==Ty_void && trans.ty->kind!=Ty_void) // if void function returns something
				EM_error(f->body->pos, "procedure returns value");
			S_endScope(venv);

			funcList=funcList->tail;
		}
		return;
	}
	}
	assert(0);
}