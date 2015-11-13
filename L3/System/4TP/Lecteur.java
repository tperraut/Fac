import java.lang.Math;

public class Lecteur extends Person
{
	Base base;

	public Lecteur(Base b)
	{
		this.base = b;
	}
	public void run()
	{
		int x;
		while(true)
		{
			x = Math.Random() * 100;
			sleep(x);
			(x % 2 == 0) ? this.lire() : this.read();
		}
	}
	public void lire()
	{
		this.b.acquerirVerrouLecteur();
		sleep(Math.Random() * 100);
		this.b.relacherVerrrouLecteur();
	}
}
