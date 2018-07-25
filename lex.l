%{
	#include "parse.tab.h"

//	int yylineno = 1;
%}

gtt			>
geq			>=
lst			<
leq			<=
ieq			<>
let			:=

delim			[ \t]
ws				{delim}+
letter		[A-Za-z]
digit			[0-9]
ident			{letter}({letter}|{digit})*
number		{digit}+(\.{digit}+)?(E[+-]{digit}+)?

%%

"if"				{ECHO; return _IF;}
"then"			{ECHO; return _THEN;}
"while"			{ECHO; return _WHILE;}
"do"				{ECHO; return _DO;}
"begin"			{ECHO; return _BEGIN;}
"end"				{ECHO; return _END;}
"call"			{ECHO; return _CALL;}
"const"			{ECHO; return _CONST;}
"procedure"	{ECHO; return _PROCEDURE;}
"var"				{ECHO; return _VAR;}
"odd"				{ECHO; return _ODD;}

{gtt}				{ECHO; return _GTT;}
{geq}				{ECHO; return _GEQ;}
{lst}				{ECHO; return _LST;}
{leq}				{ECHO; return _LEQ;}
{ieq}				{ECHO; return _IEQ;}
{let}				{ECHO; return _LET;}

"="				{ECHO; return _EQ;}
"+"				{ECHO; return _PLUS;}
"-"				{ECHO; return _SUB;}
"*"				{ECHO; return _MTP;}
"/"				{ECHO; return _DIV;}

"("				{ECHO; return _LOPER;}
")"				{ECHO; return _ROPER;}
","				{ECHO; return _COMMA;}
";"				{ECHO; return _SEMICOLON;}
"."				{ECHO; return _PERIOD;}

{ws}				{ECHO;}
{ident}			{ECHO; return _ID;}
{number}			{ECHO; return _NUM;}
"\n"				{ECHO; printf("%5ld ", cx); yylineno++;}
.					{printf("ERROR: Invalid char: %s \n", yytext);}

%%

int yywrap()
{
	return 1;
}

//int main()
//{
//	printf("%d", yylex());
//	return 0;
//}

// ===============================From sample=================================



