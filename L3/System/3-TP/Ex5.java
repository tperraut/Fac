public class Ex5 extends Thread
{
	public static final int LINE = 100;
	public static final int ROW = 100;
	private Matrice A;
	private Matrice B;
	private static Matrice RES;
	private int li;
	private int co;

	public Ex5(Matrice matA, Matrice matB, Matrice matRES, int li, int co)
	{
		this.A = matA;
		this.B = matB;
		this.RES = matRES;
		this.li = li;
		this.co = co;
	}

	@Override
	public void run()
	{
			this.RES.setv(multTable(this.A.getLi(li),
						this.B.getLi(co)),
					this.li, this.co);
	}
	private int multTable(int l1[], int l2[])
	{
		int result = 0;

		for (int i = 0; i < l1.length; i++)
			result += l1[i] * l2[i];
		return result;
	}
	public static void echoMat(Matrice M)
	{
		System.out.println(M.toString());
	}
	public static void main(String[] args)
	{
		Matrice mat1 = new Matrice(LINE, ROW, 10);
		Matrice mat2 = new Matrice(ROW, LINE, 10);
		Matrice res = new Matrice(LINE, LINE, 0); // Init res avec des 0
		Thread t = new Thread();
		ThreadGroup tg = new ThreadGroup("MM"); // Groupe de thread

		for (int i = 0; i < res.getLine(); i++)
		{
			for (int j = 0; j < res.getRow(); j++)
			{
			while (tg.activeCount() > 3){} // Ne pas lancer plus de 4 threads
			t = new Thread(tg, new Ex5(mat1, mat2.gettM(), res,
						i, j));
			t.start();
			}
		}
		while (tg.activeCount() != 0){} // Attendre la fin de tous les threads
		echoMat(RES);
	}
}
