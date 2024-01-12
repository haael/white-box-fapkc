
#include <stdio.h>

typedef signed char i8;

i8 fn_const();
i8 fn_ignore(i8);
i8 fn_identity(i8);
i8 fn_project(i8, i8);
i8 fn_inc(i8);
i8 fn_add(i8, i8);
i8 fn_cond(i8, i8);
i8 fn_conds(i8, i8);
i8 fn_loop(i8);
i8 fn_simple_loop(i8);
i8 fn_double_loop(i8);
i8 fn_inner_loop(i8);
i8 fn_cond_loop(i8);
i8 fn_ifn_for(i8);
i8 fn_for_if(i8);
i8 fn_loop_opt(i8, i8);
i8 fn_multi(i8, i8);

static const i8 l_min = -10, l_max = 10;

int main(int argc, char *argv[])
{
	i8 a, b;
	
	printf("fn_const");
	printf("\t:%d", (int)fn_const());
	printf("\n");
	
	printf("fn_ignore");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_ignore(a));
	printf("\n");
	
	printf("fn_identity");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_identity(a));
	printf("\n");
	
	printf("fn_project");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_project(a, b));
	printf("\n");
	
	printf("fn_inc");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_inc(a));
	printf("\n");
	
	printf("fn_add");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_add(a, b));
	printf("\n");
	
	printf("fn_cond");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_cond(a, b));
	printf("\n");
	
	printf("fn_conds");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_conds(a, b));
	printf("\n");
	
	printf("fn_loop");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_loop(a));
	printf("\n");
	
	printf("fn_simple_loop");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_simple_loop(a));
	printf("\n");
	
	printf("fn_double_loop");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_double_loop(a));
	printf("\n");
	
	printf("fn_inner_loop");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_inner_loop(a));
	printf("\n");
	
	printf("fn_cond_loop");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_cond_loop(a));
	printf("\n");
	
	printf("fn_ifn_for");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_ifn_for(a));
	printf("\n");
	
	printf("fn_for_if");
	for(a = l_min; a < l_max; a++)
		printf("\t%d:%d", (int)a, (int)fn_for_if(a));
	printf("\n");
	
	printf("fn_loop_opt");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_loop_opt(a, b));
	printf("\n");
	
	printf("fn_multi");
	for(a = l_min; a < l_max; a++)
		for(b = -l_max; b < l_max; b++)
			printf("\t%d,%d:%d", (int)a, (int)b, (int)fn_multi(a, b));
	printf("\n");
	
	return 0;
}

