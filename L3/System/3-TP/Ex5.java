import java.lang.Math;

public class Ex5 extends Thread
{
	public static final int LINE = 3;
	public static final int ROW = 3;
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
		mat1 = new Matrice(LINE, ROW, 10);
		mat2 = new Matrice(ROW, LINE, 10);
		res = new Matrice(LINE, LINE, 0); // Init res avec des 0
		Thread t = new Thread();
		ThreadGroup tg = new ThreadGroup("MM"); // Groupe de thread

		for (int i = 0; i < res.getLine(); i++)
		{
			for (int j = 0; j < res.getRow(); j++)
			{
				while (tg.activeCount() > 3){} // Ne pas lancer plus de 4 threads
				t = new Thread(tg, new ThreadM(mat1, mat2.gettM(), res,
							i, j));
				t.start();
			}
		}
		// Attendre la fin de tous les threads
		while (tg.activeCount() != 0){/*System.out.println("wait for it\n");*/}
		echoMat(mat1);
		echoMat(mat2);
		echoMat(res);
	}
}
