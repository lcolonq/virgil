#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lexer.h"
#include "parser.h"

static int BINARY_OPERATOR_PRECEDENCE[LAST_BINARY_OPERATOR] = {
	[BINARY_OPERATOR_STAR] = 9,
	[BINARY_OPERATOR_SLASH] = 9,
	[BINARY_OPERATOR_PERCENT] = 9,
	[BINARY_OPERATOR_PLUS] = 8,
	[BINARY_OPERATOR_MINUS] = 8,
	[BINARY_OPERATOR_LSHIFT] = 7,
	[BINARY_OPERATOR_RSHIFT] = 7,
	[BINARY_OPERATOR_LESSTHAN] = 6,
	[BINARY_OPERATOR_GREATERTHAN] = 6,
	[BINARY_OPERATOR_LESSEQUAL] = 6,
	[BINARY_OPERATOR_GREATEREQUAL] = 6,
	[BINARY_OPERATOR_EQUALEQUAL] = 5,
	[BINARY_OPERATOR_NOTEQUAL] = 5,
	[BINARY_OPERATOR_AND] = 4,
	[BINARY_OPERATOR_XOR] = 3,
	[BINARY_OPERATOR_OR] = 2,
	[BINARY_OPERATOR_ANDAND] = 1,
	[BINARY_OPERATOR_OROR] = 0,
};

static inline enum binary_operator token_to_binary_operator(enum lexer_token t) {
	switch (t) {
	case LEXER_TOKEN_STAR: return BINARY_OPERATOR_STAR;
	case LEXER_TOKEN_SLASH: return BINARY_OPERATOR_SLASH;
	case LEXER_TOKEN_PERCENT: return BINARY_OPERATOR_PERCENT;
	case LEXER_TOKEN_PLUS: return BINARY_OPERATOR_PLUS;
	case LEXER_TOKEN_MINUS: return BINARY_OPERATOR_MINUS;
	case LEXER_TOKEN_LEFTSHIFT: return BINARY_OPERATOR_LSHIFT;
	case LEXER_TOKEN_RIGHTSHIFT: return BINARY_OPERATOR_RSHIFT;
	case LEXER_TOKEN_LESSTHAN: return BINARY_OPERATOR_LESSTHAN;
	case LEXER_TOKEN_GREATERTHAN: return BINARY_OPERATOR_GREATERTHAN;
	case LEXER_TOKEN_LESSEQUAL: return BINARY_OPERATOR_LESSEQUAL;
	case LEXER_TOKEN_GREATEREQUAL: return BINARY_OPERATOR_GREATEREQUAL;
	case LEXER_TOKEN_EQUALEQUAL: return BINARY_OPERATOR_EQUALEQUAL;
	case LEXER_TOKEN_NOTEQUAL: return BINARY_OPERATOR_NOTEQUAL;
	case LEXER_TOKEN_AMPERSAND: return BINARY_OPERATOR_AND;
	case LEXER_TOKEN_CARET: return BINARY_OPERATOR_XOR;
	case LEXER_TOKEN_PIPE: return BINARY_OPERATOR_OR;
	case LEXER_TOKEN_ANDAND: return BINARY_OPERATOR_ANDAND;
	case LEXER_TOKEN_OROR: return BINARY_OPERATOR_OROR;
	default: return BINARY_OPERATOR_ERROR;
	}
}

static inline enum assignment_operator token_to_assignment_operator(enum lexer_token t) {
	switch (t) {
	case LEXER_TOKEN_EQUAL: return ASSIGNMENT_OPERATOR_EQUAL;
	case LEXER_TOKEN_STAREQUAL: return ASSIGNMENT_OPERATOR_STAREQUAL;
	case LEXER_TOKEN_SLASHEQUAL: return ASSIGNMENT_OPERATOR_SLASHEQUAL;
	case LEXER_TOKEN_PERCENTEQUAL: return ASSIGNMENT_OPERATOR_PERCENTEQUAL;
	case LEXER_TOKEN_PLUSEQUAL: return ASSIGNMENT_OPERATOR_PLUSEQUAL;
	case LEXER_TOKEN_MINUSEQUAL: return ASSIGNMENT_OPERATOR_MINUSEQUAL;
	case LEXER_TOKEN_LEFTSHIFTEQUAL: return ASSIGNMENT_OPERATOR_LSHIFTEQUAL;
	case LEXER_TOKEN_RIGHTSHIFTEQUAL: return ASSIGNMENT_OPERATOR_RSHIFTEQUAL;
	case LEXER_TOKEN_AMPERSANDEQUAL: return ASSIGNMENT_OPERATOR_AMPERSANDEQUAL;
	case LEXER_TOKEN_CARETEQUAL: return ASSIGNMENT_OPERATOR_CARETEQUAL;
	case LEXER_TOKEN_PIPEEQUAL: return ASSIGNMENT_OPERATOR_PIPEEQUAL;
	default: return ASSIGNMENT_OPERATOR_ERROR;
	}
}

struct parser_state *new_parser(char *path) {
	struct lexer_state *lexer = calloc(1, sizeof(struct lexer_state));
	if (new_lexer(lexer, path) < 0) {
		free(lexer);
		return 0;
	}
	struct parser_state *st = calloc(1, sizeof(struct parser_state));
	st->lexer = lexer;
	st->idx = 0;
	st->cur.tok = LEXER_TOKEN_ERROR;
	st->cur.start = 0;
	st->cur.end = 0;
	st->next.tok = next_token(st->lexer);
	st->next.start = st->lexer->start;
	st->next.end = st->lexer->end;
	return st;
}

enum lexer_token advance(struct parser_state *st) {
	if (!st) return LEXER_TOKEN_ERROR;
	st->cur.tok = st->next.tok;
	st->cur.start = st->next.start;
	st->cur.end = st->next.end;
	st->next.tok = next_token(st->lexer);
	st->next.start = st->lexer->start;
	st->next.end = st->lexer->end;
	return st->cur.tok;
}

int match(struct parser_state *st, enum lexer_token expected) {
	if (st && st->next.tok == expected) {
		advance(st);
		return 1;
	} else {
		return 0;
	}
}

enum lexer_token peek(struct parser_state *st) {
	if (!st) return LEXER_TOKEN_ERROR;
	return st->next.tok;
}

void current_token_string(struct parser_state *st, char *buf, int buflen) {
	int len;

	len = st->cur.end - st->cur.start;
	if (len > buflen - 2) len = buflen - 2;
	memcpy(buf, st->lexer->input + st->cur.start, len);
	buf[len] = 0;
}

void indent(int c) {
	int i;
	for (i = 0; i < c; ++i) putchar(' ');
}

void print_identifier(int c, struct identifier *it) {
	indent(c);
	if (it && it->name) printf("%s\n", it->name);
	else printf("NULL\n");
}
struct identifier *parse_identifier(struct parser_state *st) {
	struct identifier *ret;

	if (peek(st) == LEXER_TOKEN_IDENTIFIER) {
		advance(st);
		ret = calloc(1, sizeof(struct identifier));
		ret->name = calloc(256, sizeof(char));
		current_token_string(st, ret->name, 256);
		return ret;
	} else {
		return 0;
	}
}

void print_constant(int c, struct constant *it) {
	indent(c);
	if (it) {
		switch (it->sort) {
		case CONSTANT_INTEGER:
			printf("%ld\n", it->contents.integer);
			break;
		case CONSTANT_FLOATING:
			printf("%lf\n", it->contents.floating);
			break;
		case CONSTANT_ENUMERATION:
			printf("%s\n", it->contents.enumeration);
			break;
		case CONSTANT_CHARACTER:
			printf("'%c'\n", it->contents.character);
			break;
		default:
			printf("<unknown constant %d>\n", it->sort);
			break;
		}
	} else printf("NULL\n");
}
void print_primary_expression(int c, struct primary_expression *it) {
	indent(c);
	if (it) {
		printf("primary_expression ");
		switch (it->sort) {
		case PRIMARY_EXPRESSION_IDENTIFIER:
			printf("identifier:\n");
			print_identifier(c + 1, it->contents.ident);
			break;
		case PRIMARY_EXPRESSION_CONSTANT:
			printf("constant:\n");
			print_constant(c + 1, it->contents.constant);
			break;
		default: printf("<unknown sort %d>\n", it->sort); break;
		}
	} else printf("NULL\n");
}
struct primary_expression *parse_primary_expression(struct parser_state *st) {
	enum lexer_token t;
	struct primary_expression *ret;
	char buf[256];

	ret = calloc(1, sizeof(struct primary_expression));
	t = peek(st);
	switch (t) {
	case LEXER_TOKEN_IDENTIFIER:
		ret->sort = PRIMARY_EXPRESSION_IDENTIFIER;
		ret->contents.ident = parse_identifier(st);
		break;
	case LEXER_TOKEN_DECIMALLITERAL:
		advance(st);
		current_token_string(st, buf, sizeof(buf));
		ret->sort = PRIMARY_EXPRESSION_CONSTANT;
		ret->contents.constant = calloc(1, sizeof(struct constant));
		ret->contents.constant->sort = CONSTANT_INTEGER;
		ret->contents.constant->contents.integer = atol(buf);
		break;
	case LEXER_TOKEN_CHARLITERAL:
		advance(st);
		current_token_string(st, buf, sizeof(buf));
		ret->sort = PRIMARY_EXPRESSION_CONSTANT;
		ret->contents.constant = calloc(1, sizeof(struct constant));
		ret->contents.constant->sort = CONSTANT_CHARACTER;
		ret->contents.constant->contents.character = buf[1];
		break;
	case LEXER_TOKEN_LEFTPAREN:
		advance(st);
		ret->sort = PRIMARY_EXPRESSION_PARENTHESIZED;
		ret->contents.parenthesized = parse_expression(st);
		if (!match(st, LEXER_TOKEN_RIGHTPAREN)) goto exit;
		break;
	default:
	exit:
		free(ret);
		ret = NULL;
		break;
	}
	return ret;
}

void print_argument_list(int c, struct postfix_expression_funcall *it) {
	int i;
	indent(c);
	if (it) {
		printf("argument_list\n");
		for (i = 0; i < it->args_len; ++i) {
			print_assignment_expression(c + 1, it->args[i]);
		}
	} else printf("NULL\n");
}
struct postfix_expression_funcall *parse_argument_list(struct parser_state *st) {
	struct postfix_expression_funcall *ret;
	int buflen;

	ret = calloc(1, sizeof(struct postfix_expression_funcall));
	ret->args_len = 0;
	buflen = 32;
	ret->args = calloc(buflen, sizeof(struct assignment_expression));

	ret->args[ret->args_len++] = parse_assignment_expression(st);
	while (peek(st) == LEXER_TOKEN_COMMA) {
		advance(st);
		ret->args[ret->args_len++] = parse_assignment_expression(st);
		if (ret->args_len >= buflen)
			ret->args = reallocarray(ret->args, buflen <<= 1, sizeof(struct assignment_expression *));
	}

	return ret;
}

void print_postfix_expression(int c, struct postfix_expression *it) {
	int i;
	indent(c);
	if (it && it->base) {
		printf("postfix_expression:\n");
		switch (it->base->sort) {
		case POSTFIX_EXPRESSION_BASE_PRIMARY:
			print_primary_expression(c + 1, it->base->contents.primary);
			break;
		default: break;
		}
		for (i = 0; i < it->exts_len; ++i) {
			switch (it->exts[i].sort) {
			case POSTFIX_EXPRESSION_EXT_INDEX:
				indent(c + 1); printf("index:\n");
				print_expression(c + 2, it->exts[i].contents.index);
				break;
			case POSTFIX_EXPRESSION_EXT_FUNCALL:
				indent(c); printf("funcall:\n");
				print_argument_list(c + 2, it->exts[i].contents.funcall);
				break;
			case POSTFIX_EXPRESSION_EXT_MEMBER:
				indent(c + 1); printf("member:\n");
				print_identifier(c + 2, it->exts[i].contents.member);
				break;
			case POSTFIX_EXPRESSION_EXT_MEMBER_ARROW:
				indent(c + 1); printf("member:\n");
				print_identifier(c + 2, it->exts[i].contents.member);
				break;
			case POSTFIX_EXPRESSION_EXT_PLUSPLUS:
				indent(c + 1); printf("++\n");
				break;
			case POSTFIX_EXPRESSION_EXT_MINUSMINUS:
				indent(c + 1); printf("--\n");
				break;
			default:
				break;
			}
		}
	} else printf("NULL\n");
}
struct postfix_expression *parse_postfix_expression(struct parser_state *st) {
	enum lexer_token t;
	struct postfix_expression *ret;
	int buflen;

	ret = calloc(1, sizeof(struct postfix_expression));
	ret->base = calloc(1, sizeof(struct postfix_expression_base));
	ret->base->sort = POSTFIX_EXPRESSION_BASE_PRIMARY;
	ret->base->contents.primary = parse_primary_expression(st);
	ret->exts_len = 0;
	buflen = 32;
	ret->exts = calloc(buflen, sizeof(struct postfix_expression_ext));

	while ((t = peek(st)) > 0) {
		switch (t) {
		case LEXER_TOKEN_LEFTSQUARE:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_INDEX;
			ret->exts[ret->exts_len].contents.index = parse_expression(st);
			ret->exts_len++;
			if (!match(st, LEXER_TOKEN_RIGHTSQUARE)) goto exit;
			break;
		case LEXER_TOKEN_LEFTPAREN:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_FUNCALL;
			ret->exts[ret->exts_len].contents.funcall = parse_argument_list(st);
			ret->exts_len++;
			if (!match(st, LEXER_TOKEN_RIGHTPAREN)) goto exit;
			break;
		case LEXER_TOKEN_DOT:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_MEMBER;
			ret->exts[ret->exts_len].contents.member = parse_identifier(st);
			ret->exts_len++;
			break;
		case LEXER_TOKEN_ARROW:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_MEMBER_ARROW;
			ret->exts[ret->exts_len].contents.member = parse_identifier(st);
			ret->exts_len++;
			break;
		case LEXER_TOKEN_PLUSPLUS:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_PLUSPLUS;
			ret->exts_len++;
			break;
		case LEXER_TOKEN_MINUSMINUS:
			advance(st);
			ret->exts[ret->exts_len].sort = POSTFIX_EXPRESSION_EXT_MINUSMINUS;
			ret->exts_len++;
			break;
		default:
			goto exit;
		}
		if (ret->exts_len >= buflen)
			ret->exts = reallocarray(ret->exts, buflen <<= 1, sizeof(struct postfix_expression_ext));
	}

exit:
	return ret;
}

void print_unary_expression(int c, struct unary_expression *it) {
	indent(c);
	if (it) {
		printf("unary_expression ");
		switch (it->sort) {
		case UNARY_EXPRESSION_POSTFIX:
			printf("postfix:\n");
			print_postfix_expression(c + 1, it->contents.postfix);
			break;
		default: printf("<unknown sort %d>\n", it->sort); break;
		}
	} else printf("NULL\n");
}
struct unary_expression *parse_unary_expression(struct parser_state *st) {
	struct unary_expression *ret;
	ret = calloc(1, sizeof(struct unary_expression));
	ret->sort = UNARY_EXPRESSION_POSTFIX;
	ret->contents.postfix = parse_postfix_expression(st);
	return ret;
}

void print_binary_expression(int c, struct binary_expression *it) {
	int i;
	indent(c);
	if (it && it->base) {
		printf("binary_expression:\n");
		print_unary_expression(c + 1, it->base);
		for (i = 0; i < it->exts_len; ++i) {
			switch (it->exts[i].op) {
			case BINARY_OPERATOR_STAR:
				indent(c + 1); printf("*\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_SLASH:
				indent(c + 1); printf("/\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_PERCENT:
				indent(c + 1); printf("%%\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_PLUS:
				indent(c + 1); printf("+\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_MINUS:
				indent(c + 1); printf("-\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_LSHIFT:
				indent(c + 1); printf("<<\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_RSHIFT:
				indent(c + 1); printf(">>\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_LESSTHAN:
				indent(c + 1); printf("<\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_GREATERTHAN:
				indent(c + 1); printf(">\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_LESSEQUAL:
				indent(c + 1); printf("<=\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_GREATEREQUAL:
				indent(c + 1); printf(">=\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_EQUALEQUAL:
				indent(c + 1); printf("==\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_NOTEQUAL:
				indent(c + 1); printf("!=\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_AND:
				indent(c + 1); printf("&\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_XOR:
				indent(c + 1); printf("^\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_OR:
				indent(c + 1); printf("|\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_ANDAND:
				indent(c + 1); printf("&&\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			case BINARY_OPERATOR_OROR:
				indent(c + 1); printf("||\n");
				print_binary_expression(c + 1, it->exts[i].expr);
				break;
			default:
				break;
			}
		}
	} else printf("NULL\n");
}
// parse a nested binary expression with precedence climbing
struct binary_expression *parse_binary_expression(struct parser_state *st, int p) {
	enum lexer_token t;
	enum binary_operator b;
	struct binary_expression *ret;
	int buflen;

	ret = calloc(1, sizeof(struct binary_expression));
	ret->base = parse_unary_expression(st);
	ret->exts_len = 0;
	buflen = 32;
	ret->exts = calloc(buflen, sizeof(struct binary_expression_ext));
	while ((t = peek(st)) > 0 && (b = token_to_binary_operator(t)) > 0 && BINARY_OPERATOR_PRECEDENCE[b] >= p) {
		advance(st);
		ret->exts[ret->exts_len].op = b;
		ret->exts[ret->exts_len].expr = parse_binary_expression(st, p + 1);
		++ret->exts_len;
		if (ret->exts_len >= buflen)
			ret->exts = reallocarray(ret->exts, buflen <<= 1, sizeof(struct binary_expression_ext));
	}

	return ret;
}

void print_conditional_expression(int c, struct conditional_expression *it) {
	indent(c);
	if (it && it->cond) {
		printf("conditional_expression:\n");
		print_binary_expression(c + 1, it->cond);
		if (it->then) {
			indent(c + 1); printf("then:\n");
			print_expression(c + 2, it->then);
		}
		if (it->els) {
			indent(c + 1); printf("else:\n");
			print_conditional_expression(c + 2, it->els);
		}
	} else printf("NULL\n");
}
struct conditional_expression *parse_conditional_expression(struct parser_state *st) {
	struct conditional_expression *ret;
	ret = calloc(1, sizeof(struct conditional_expression));
	ret->cond = parse_binary_expression(st, 0);
	if (peek(st) == LEXER_TOKEN_QUESTION) {
		advance(st);
		ret->then = parse_expression(st);
		if (peek(st) == LEXER_TOKEN_COLON) {
			advance(st);
			ret->els = parse_conditional_expression(st);
		}
	}
	return ret;
}

void print_assignment_expression(int c, struct assignment_expression *it) {
	indent(c);
	if (it && it->left) {
		printf("assignment_expression");
		switch (it->op) {
		case ASSIGNMENT_OPERATOR_EQUAL:
			printf(" =");
			break;
		case ASSIGNMENT_OPERATOR_STAREQUAL:
			printf(" *=");
			break;
		case ASSIGNMENT_OPERATOR_SLASHEQUAL:
			printf(" /=");
			break;
		case ASSIGNMENT_OPERATOR_PERCENTEQUAL:
			printf(" %%=");
			break;
		case ASSIGNMENT_OPERATOR_PLUSEQUAL:
			printf(" +=");
			break;
		case ASSIGNMENT_OPERATOR_MINUSEQUAL:
			printf(" -=");
			break;
		case ASSIGNMENT_OPERATOR_LSHIFTEQUAL:
			printf(" <<=");
			break;
		case ASSIGNMENT_OPERATOR_RSHIFTEQUAL:
			printf(" >>=");
			break;
		case ASSIGNMENT_OPERATOR_AMPERSANDEQUAL:
			printf(" &=");
			break;
		case ASSIGNMENT_OPERATOR_CARETEQUAL:
			printf(" ^=");
			break;
		case ASSIGNMENT_OPERATOR_PIPEEQUAL:
			printf(" |=");
			break;
		default:
			break;
		}
		printf(":\n");
		print_conditional_expression(c + 1, it->left);
		if (it->right) {
			print_assignment_expression(c + 1, it->right);
		}
	} else printf("NULL\n");
}
struct assignment_expression *parse_assignment_expression(struct parser_state *st) {
	enum lexer_token t;
	enum assignment_operator b;
	struct assignment_expression *ret;
	ret = calloc(1, sizeof(struct assignment_expression));
	ret->left = parse_conditional_expression(st);

	t = peek(st);
	b = token_to_assignment_operator(t);
	if (b > 0) {
		advance(st);
		ret->op = b;
		ret->right = parse_assignment_expression(st);
	}
	return ret;
}

void print_expression(int c, struct expression *it) {
	int i;
	indent(c);
	if (it) {
		printf("expression:\n");
		for (i = 0; i < it->assignments_len; ++i) {
			print_assignment_expression(c + 1, it->assignments[i]);
		}
	} else printf("NULL\n");
}
struct expression *parse_expression(struct parser_state *st) {
	struct expression *ret;
	int buflen;

	ret = calloc(1, sizeof(struct postfix_expression_funcall));
	ret->assignments_len = 0;
	buflen = 32;
	ret->assignments = calloc(buflen, sizeof(struct assignment_expression));

	ret->assignments[ret->assignments_len++] = parse_assignment_expression(st);
	while (peek(st) == LEXER_TOKEN_COMMA) {
		advance(st);
		ret->assignments[ret->assignments_len++] = parse_assignment_expression(st);
		if (ret->assignments_len >= buflen)
			ret->assignments = reallocarray(ret->assignments, buflen <<= 1, sizeof(struct assignment_expression *));
	}

	return ret;
}

int main () {
	struct parser_state *st;
	struct expression *node;

	st = new_parser("test.c");
	node = parse_expression(st);
	print_expression(0, node);
};
