import java.lang.Math;

public class Graphes {
    public static void main(String[] args) {

	///*
	// Exemple (a)
	// 2 - sqrt(2);  ~ 0.5858
	Noeud as1  = new NSource(2);
	Noeud aop1 = new NRacine(as1);
	Noeud aop2 = new NMoins(aop1);
	Noeud aop3 = new NAdd(as1, aop2);
	System.out.println("Exemple (a) : " + aop3.compute());
	//*/

	///*
	// Exemple (b)
	// min(1, 2);    ~ 1
	Noeud bs1  = new NSource(1);
	Noeud bs2  = new NSource(2);
	Noeud bop1 = new NMoins(bs2);
	Noeud bop2 = new NAdd(bs1, bop1);
	Noeud bop3 = new NChoix(bs1, bs2, bop2, 0);
	System.out.println("Exemple (b) : " + bop3.compute());
	//*/

	///*
	// Exemple (c)
	// Partie entière de 4.2;    ~4
	Noeud cs0  = new NSource(0);
	Noeud cs1  = new NSource(1);
	Noeud cc1  = new NCompteur();
	NoeudBinaire cop1 = new NAdd(cs1);
	Noeud cop2 = new NChoix(cop1, cs0, cc1, 4.2);
	cop1.setSource2(cop2);
	System.out.println("Exemple (c) : " + cop2.compute());
	//*/

	///*
	// Exemple (d)
	// sqrt(2)*sqrt(2);   ~2
	Noeud ds1  = new NSource(2);
	Noeud dop1 = new NRacine(ds1);
	Noeud dop2 = new NPuissance(dop1, 2);
	System.out.println("Exemple (d) : " + dop2.compute());
	//*/

	///*
	// Exemple (e)
	// 0.999999999 puissance 100;   ~0.0000454
	Noeud es1  = new NSource(0.999999999);
	Noeud ec1  = new NCompteur();
	Noeud eop1 = new NPuissance(10);
	Noeud eop2 = new NChoix(eop1, es1, ec1, 11);
	eop1.setSource1(eop2);
	System.out.println("Exemple (e) : " + eop2.compute());
	//*/
    }
}

abstract class Noeud
{
    public Noeud() { }
    abstract public double compute();
}

abstract class NoeudUnaire extends Noeud
{
	protected Noeud source1;

	public NoeudUnaire() {}
	public void setSource1(Noeud n)
	{
		this.source1 = n;
	}
}

abstract class NoeudBinaire extends NoeudUnaire
{
	protected Noeud source2;

	public NoeudBinaire() {}
	public void setSource2(Noeud n)
	{
		this.source2 = n;
	}
}
class NSource extends Noeud
{
	private double cst;

	public NSource(double d)
	{
		this.cst = d;
	}
	public double compute()
	{
		return (cst);
	}
}

class NChoix extends Noeud
{
	private Noeud source1;
	private Noeud source2;
	private Noeud source3;
	private double seuil;

	public NChoix (Noeud src1, Noeud src2, Noeud src3, double d)
	{
		source1 = src1;
		source2 = src2;
		source3 = src3;
		seuil = d;
	}

	public double compute()
	{
		if (this.source3.compute() < this.seuil)
			return (this.source1.compute());
		else
			return (this.source2.compute());
	}
}

class NCompteur extends Noeud
{
	private static double n = 0;

	public NCompteur() {}
	public double compute()
	{
		return (++n);
	}
}

class NPuissance extends NoeudUnaire
{
	private int n;

	public NPuissance(Noeud src, int nb)
	{
		setSource1(src);
		this.n = nb;
	}
	public NPuissance(int nb)
	{
		this.n = nb;
	}
	private double expRapide(double x, int n)
	{
		if (n == 0 || x == 1)
			return (1);
		if (x == 0)
			return (0);
		if (n % 2 == 0)
			return (expRapide(x * x, n / 2));
		return (expRapide(x * x, n / 2) * x);
	}
	public double compute()
	{
		return (expRapide(source1.compute(), this.n));
	}
}

class NMoins extends NoeudUnaire
{
	public NMoins(Noeud n)
	{
		setSource1(n);
	}
	public double compute()
	{
		return (- source1.compute());
	}
}

class NRacine extends NoeudUnaire
{
	public NRacine(Noeud n)
	{
		setSource1(n);
	}
	public double compute()
	{
		return (Math.sqrt(source1.compute()));
	}
}

class NAdd extends NoeudBinaire
{
	public NAdd(Noeud no1, Noeud no2)
	{
		setSource1(no1);
		setSource2(no2);
	}
	public NAdd(Noeud n1)
	{
		setSource1(n1);
	}
	public double compute()
	{
		return (source1.compute() + source2.compute());
	}
}

class NMult extends NoeudBinaire
{
	public NMult(Noeud no1, Noeud no2)
	{
		setSource1(no1);
		setSource2(no2);
	}
	public double compute()
	{
		return (source1.compute() * source2.compute());
	}
}
