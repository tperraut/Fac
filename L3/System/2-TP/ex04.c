#include <pthread.h>
#include <unistd.h>

static void	routine(void)
{
	for(int i = 0; i < 10; i++)
	{
		sleep(1);
		write(1,"Bonjour\n", 8);
	}
}

int	main(void)
{
	void	*p;

	p = routine;
	pthread_t t;
	pthread_create (&t, NULL, p, "");
	//pthread_join(t, NULL);
	return (0);
}
