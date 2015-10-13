import java.lang.Math;

public class Ecrivain extends Lecteur
{
	public Ecrivain(Base b) {super(b)}
	public void read()
	{
		this.b.acquerirVerrouEcrivain();
		sleep(Math.Random() * 100);
		this.b.relacherVerrouEcrivain();
	}
}
