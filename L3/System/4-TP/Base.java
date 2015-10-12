import java.util.concurrent.Semaphore;

public class Base
{
	static int nbLecteurs = 0;
	Semaphore write = new Semaphore(1);
	Semaphore read = new Semaphore(1);

	void acquerirVerrouEcrivain() throws InterruptedException
	{
		write.acquire();
	}
	void acquerirVerrouLecteur() throws InterruptedException
	{
		read.acquire();
		if (nbLecteurs == 0)
			write.acquire();
		++nbLecteurs;
		read.release();
	}
	void relacherVerrouEcrivain() throws InterruptedException
	{
		write.release();
	}
	void relacherVerrouLecteur() throws InterruptedException
	{
		read.acquire();
		--nbLecteurs;
		if (nbLecteurs == 0)
			write.release();
		read.release();
	}
	public static void main(String[] args)
	{
	}
}
