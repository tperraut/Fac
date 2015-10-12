import java.lang.Math;

public class MMperLine extends Thread
{
	// Nbr de ligne de mat1, de colonne de mat2 et de ligne/colonne de res
	public static final int LINE = 10;
	// Nbr de colonne de mat1 et de ligne de mat2
	public static final int ROW = 9;
	static Matrice mat1;
	static Matrice mat2;
	static Matrice res;

	public static void echoMat(Matrice M)
	{
		System.out.println(M.toString());
	}
	public static void setVtoRes(Matrice m, int v, int li, int co)
	{
		m.setv(v, li, co);
	}
	public static void main(String[] args)
	{
		// Un autre constructeur de matrice est disponible, vois Matrice.java
		mat1 = new Matrice(LINE, ROW, 10);
		mat2 = new Matrice(ROW, LINE, 10);
		res = new Matrice(LINE, LINE, 0); // Init res avec des 0
		Thread t = new Thread();
		ThreadGroup tg = new ThreadGroup("MM"); // Groupe de thread

		for (int i = 0; i < res.getLine(); i++)
		{
			while (tg.activeCount() > 3){} // Ne pas avoir plus de 4 threads actif
			t = new Thread(tg, new ThreadML(mat1, mat2.gettM(), res, i));
			t.start();
			if (i / 100 > 0 && i % 100 == 0)
				tg.list();
		}
		// Attendre la fin de tous les threads
		while (tg.activeCount() != 0){
			//System.out.println("wait for it\n");
		}
		try{t.join();}
		catch(Exception e){}
		System.out.println(tg.toString() + "\n");
		mat1.echo();
		System.out.println("");
		mat2.echo();
		System.out.println("");
		res.echo();
	}
}
