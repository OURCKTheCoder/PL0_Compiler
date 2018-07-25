%{
	#include <stdio.h>
	#include <string.h>
	#include <stdlib.h>
	
	int yyerror(char * msg);
	FILE * yyin;
	extern char * yytext;
	extern int yylex();
	
//	extern int yylineno; // Windows & Linux independent
	
// ===============================From sample=================================
	
	#define txmax       100            // length of identifier table
	#define al          10             // length of identifiers
	#define amax        2047           // maximum address
	#define levmax      3              // maximum depth of block nesting
	#define cxmax       2000           // size of code array
	
	char * err_msg[] =
	{
	/*  0 */    "",
	/*  1 */    "Found ':=' when expecting '='.",
	/*  2 */    "There must be a number to follow '='.",
	/*  3 */    "There must be an '=' to follow the identifier.",
	/*  4 */    "There must be an identifier to follow 'const', 'var', or 'procedure'.",
	/*  5 */    "Missing ',' or ';'.",
	/*  6 */    "Incorrect procedure name.",
	/*  7 */    "Statement expected.",
	/*  8 */    "Follow the statement is an incorrect symbol.",
	/*  9 */    "'.' expected.",
	/* 10 */    "';' expected.",
	/* 11 */    "Undeclared identifier.",
	/* 12 */    "Illegal assignment.",
	/* 13 */    "':=' expected.",
	/* 14 */    "There must be an identifier to follow the 'call'.",
	/* 15 */    "A constant or variable can not be called.",
	/* 16 */    "'then' expected.",
	/* 17 */    "';' or 'end' expected.",
	/* 18 */    "'do' expected.",
	/* 19 */    "Incorrect symbol.",
	/* 20 */    "Relative operators expected.",
	/* 21 */    "Procedure identifier can not be in an expression.",
	/* 22 */    "Missing ')'.",
	/* 23 */    "The symbol can not be followed by a factor.",
	/* 24 */    "The symbol can not be as the beginning of an expression.",
	/* 25 */    "",
	/* 26 */    "",	
	/* 27 */    "",
	/* 28 */    "",
	/* 29 */    "",
	/* 30 */    "",
	/* 31 */    "The number is too great.",
	/* 32 */    "There are too many levels."
	};
	
	// Types of ID table
	enum object
	{
		 constant, variable, proc
	};

   // Functions
	enum fct
	{
		 lit, opr, lod, sto, cal, Int, jmp, jpc
	};	
	
	// ID table definition
	struct
	{
		 char name[al + 1];
		 enum object kind;
		 long val;
		 long level;
		 long addr;
	} table[txmax + 1];
	
	// Instruuction definition
	typedef struct
	{
		 enum fct f;		// function code
		 long l; 			// level
		 long a; 			// displacement address
	} instruction;
	
	typedef struct
	{
		long cx;
		int dx;
		int tx;
		char id[al+1];
		int op;
	} state;
	state stateStack[20];	//状态栈，当嵌套过程 / 过程不连续时时保存状态。 TODO 考虑优化，减少字段
	int stateStack_ptr = 0;
	
	//指存
	instruction code[cxmax+1];
	char mnemonic[8][3+1];
	
	char id[al+1];         // last identifier read
	long num;              // last number read
	long cx;               // code allocation index
	
	// the following variables for block
	long dx;						// data allocation index 语法分析过程中处理
	long lev;					// current depth of block nesting.语法分析过程中处理
	long tx;						// current table index
	
	void enter(enum object k);
	void gen(enum fct x, long y, long z);
	void listcode(long cx0);
	void error(long msg);
	long position(char* id);
%}

%token WPCHAR
%token _GTT _GEQ _LST _LEQ _IEQ _PLUS _SUB _MTP	_DIV _EQ _LET
%token _LOPER _ROPER _COMMA _SEMICOLON _PERIOD
%token _BEGIN _IF _THEN _WHILE _DO _END _CALL _CONST _PROCEDURE _VAR _ODD
%token _ID _NUM

%%
// Some of these rules were translated into non-left-recrusive one.
Program				:	Block _PERIOD
							{ 
								printf("\n----------------------------------------------\n");
								printf("\n - Program pass! \n");
								
//									DEBUG 1. ID table
//									printf("\n-------------------------------------------\n");
//									for(int i = 1; i < 14; i++)
//									{
//										printf("\n<tx = %d, addr = %ld, name = %s, lev = %ld, val = %ld>\n"
//											, i, table[i].addr, table[i].name, table[i].level, table[i].val);
//									}

//									DEBUG 2. P-Code
//									printf("\n-------------------------------------------\n");
//									listcode(0);

								exit(0);
							}
						;

Block					:	{
								dx = 3; gen(jmp,0,0); table[tx].addr = cx;
								if(lev>levmax) error(32);
								state st; st.tx = tx;
								stateStack[stateStack_ptr++] = st;
							}
							ConstDecl VarDecl ProcDecl 
							{
								int previousTx = stateStack[--stateStack_ptr].tx;
								code[table[previousTx].addr].a = cx;	// TODO ?
								table[previousTx].addr = cx;
								// 用于增量打印
								state st; st.cx = cx; stateStack[stateStack_ptr++] = st;
								gen(Int,0,dx);
							}
							Stmt
							{
								gen(opr,0,0);
								int previousCx = stateStack[--stateStack_ptr].cx;
								listcode(previousCx);
							}
						;
	
ConstDecl			:	_CONST ConstDef ConstDeclLst _SEMICOLON
						|	/* Empty */
						;
			
ConstDeclLst		:	_COMMA ConstDef ConstDeclLst
						|	/* Empty */
						;
			
ConstDef 			:	_ID {strcpy(id, yytext);} _EQ _NUM {num = atoi(yytext); enter(constant);}
						;
			
VarDecl				:	_VAR _ID {strcpy(id, yytext); enter(variable);} VarDeclList _SEMICOLON
						|	/* Empty */
						;

VarDeclList			:	_COMMA _ID {strcpy(id, yytext); enter(variable);} VarDeclList
						|	/* Empty */
						;
	
ProcDecl				:	_PROCEDURE _ID 
							{
								strcpy(id, yytext); enter(proc);
								lev++;
								state st; st.dx = dx; st.tx = tx;
								stateStack[stateStack_ptr++] = st;
							} 
							_SEMICOLON
							Block 
							{
								lev--;
								state st = stateStack[--stateStack_ptr];
								dx = st.dx; tx = st.tx;
							}
							_SEMICOLON
							ProcDeclList
						|	/* Empty */
						;

ProcDeclList		:	_PROCEDURE _ID 
							{
								strcpy(id, yytext); enter(proc);
								lev++;
								state st; st.dx = dx; st.tx = tx;
								stateStack[stateStack_ptr++] = st;
							}
							_SEMICOLON
							Block _SEMICOLON 
							{
								lev--;
								state st = stateStack[--stateStack_ptr];
								dx = st.dx; tx = st.tx;
							}
							ProcDeclList
						|	/* Empty */
						;
			
Stmt					:	_ID
							{
								state st; strcpy(st.id, yytext);
								stateStack[stateStack_ptr++] = st;
							}
							_LET Exp 
							{
								char * previousId = stateStack[--stateStack_ptr].id;
								long i = position(previousId); 
								if(i == 0) error(11);
								else if(table[i].kind!=variable) error(12);
//								printf("%s \n", previousId);
								gen(sto, lev-table[i].level, table[i].addr);
							}
						|	_CALL _ID 
							{
								strcpy(id, yytext);
								int i = position(id);
				            if(i == 0) error(11);
								else if(table[i].kind==proc)
									 gen(cal,lev-table[i].level,table[i].addr);
								else error(15);
							}
						|	_BEGIN Stmt StmtList _END
						|	_IF Cond _THEN 
							{
								state st; st.cx = cx;
								stateStack[stateStack_ptr++] = st;
								gen(jpc,0,0);
							}
							Stmt 
							{
								long previousCx = stateStack[--stateStack_ptr].cx;
								code[previousCx].a=cx;
							}
						|	_WHILE 
							{
								state st; st.cx = cx;
								stateStack[stateStack_ptr++] = st;
							}
							Cond 
							{
								state st; st.cx = cx;
								stateStack[stateStack_ptr++] = st;
								gen(jpc,0,0);
							}
							_DO Stmt
							{
								long cx2 = stateStack[--stateStack_ptr].cx;
								long cx1 = stateStack[--stateStack_ptr].cx;
								gen(jmp,0,cx1); code[cx2].a = cx;
							}
						|	/* Empty. */ /* TODO Is this currect?*/
						;
			
StmtList				:	_SEMICOLON Stmt StmtList
						|	/* Empty */
						;
			
Cond					:	_ODD Exp {gen(opr, 0, 6);}
						|	Exp RelOp Exp
							{
								int relop = stateStack[--stateStack_ptr].op;
								switch(relop)
								{
									 case _EQ:
										  gen(opr, 0, 8);
										  break;

									 case _IEQ:
										  gen(opr, 0, 9);
										  break;

									 case _LST:
										  gen(opr, 0, 10);
										  break;

									 case _GEQ:
										  gen(opr, 0, 11);
										  break;

									 case _GTT:
										  gen(opr, 0, 12);
										  break;

									 case _LEQ:
										  gen(opr, 0, 13);
										  break;
								}
							}
						;
						
// TODO RelOp只会从Cond产生式产生，因此允许这么做
RelOp					:	_EQ	{state st; st.op = _EQ; stateStack[stateStack_ptr++] = st;}
						|	_IEQ	{state st; st.op = _IEQ; stateStack[stateStack_ptr++] = st;}
						|	_LST	{state st; st.op = _LST; stateStack[stateStack_ptr++] = st;}
						|	_GTT	{state st; st.op = _GTT; stateStack[stateStack_ptr++] = st;}
						|	_LEQ	{state st; st.op = _LEQ; stateStack[stateStack_ptr++] = st;}
						|	_GEQ	{state st; st.op = _GEQ; stateStack[stateStack_ptr++] = st;}
						;
			
Exp					:	_PLUS Term TermList						// Positive exp.
						|	_SUB Term {gen(opr,0,1);} TermList 	// Negative exp. TODO Currect?
						|	Term TermList
						;

// Not exactly the same as before...			
TermList				:	_PLUS Term {gen(opr,0,2);} TermList
						|	_SUB Term {gen(opr,0,3);} TermList
						|	/* Empty */
						;
			
Term					:	Factor FactorList
						;

FactorList			:	_MTP Factor { gen(opr,0,4); } FactorList
						|	_DIV Factor { gen(opr,0,5); } FactorList
						|	/* Empty */
						;
			
Factor				:	_ID
							{
								strcpy(id, yytext);
								long i = position(id);
								
								if(i == 0)
									 error(11);
								else
								{
									 switch(table[i].kind)
									 {
										  case constant:
												gen(lit, 0, table[i].val);
												break;

										  case variable:
												gen(lod, lev-table[i].level, table[i].addr);
												break;

										  case proc:
												error(21);
												break;
									 }
								}
							}
						|	_NUM { num = atoi(yytext); gen(lit,0,num); }
						|	_LOPER Exp _ROPER
						;
				
%%

#include "lex.yy.c"

int yyerror(char* msg)
{
	printf("Error: %s encountered at line number:%d\n", msg, yylineno);
}

int main()
{
	strcpy(mnemonic[lit],"LIT");
	strcpy(mnemonic[opr],"OPR");
	strcpy(mnemonic[lod],"LOD");
	strcpy(mnemonic[sto],"STO");
	strcpy(mnemonic[cal],"CAL");
	strcpy(mnemonic[Int],"INT");
	strcpy(mnemonic[jmp],"JMP");
	strcpy(mnemonic[jpc],"JPC");

	char path[50];
	printf(" - PL/0 Analyzer: Input your program path here: ");
	scanf("%s", path);
	
	if((yyin = fopen(path,"r")) == NULL)
	{
		printf(" - File not exist! Input your program here. ");
	}
	
	printf("\n----------------------------------------------\n");
   cx = 0; lev = 0; tx = 0;
	
	printf("%5ld ", cx); // TODO 第一行的打印应该放在lex里面...
	yyparse();
	
	return 0;
}

// ===============================From sample=================================

void error(long n)
{
    long i;

    printf("\n[!]Error => ");
    printf("(%ld)%s \n", n, err_msg[n]);
}


void enter(enum object k)		// enter object into table.This fx should be in lexer.
{
    tx = tx + 1;
    strcpy(table[tx].name, id);
    table[tx].kind = k;
    switch(k)
    {
        case constant:
				if(num > amax)
				{
					error(31);
					num = 0;
				}
            table[tx].val = num;
            break;

        case variable:
            table[tx].level = lev; table[tx].addr = dx; dx = dx + 1;
            break;

        case proc:
            table[tx].level = lev;
            break;
    }
}

void gen(enum fct x, long y, long z)
{
	if(cx > cxmax)
	{
	  printf("Program too long\n");
	  exit(1);
	}
	code[cx].f = x; code[cx].l = y; code[cx].a = z;
	cx = cx + 1;
}

void listcode(long cx0)         // list code generated for this block
{
	long i;
	printf("\n");
	for(i = cx0; i <= cx-1; i++)
	{
	  printf("%10ld%5s%3ld%5ld\n", i, mnemonic[code[i].f], code[i].l, code[i].a);
	}
}

long position(char * id)         // find identifier id in table
{
    long i;
    strcpy(table[0].name, id);	// table[0] is reserved - as a flag for "Can't find".
    i = tx;
    while(strcmp(table[i].name, id) != 0)
    {
        i = i - 1;
    }
    return i;
}
