import java.lang.Math;

public class Matrice
{
	private int row;
	private int line;
	private int M[][];

	public Matrice(int Ma[][])
	{
		this.line = Ma.length;
		this.row = Ma[0].length;
		this.M = Ma;
	}
	public Matrice(int line, int row, int rand)
	{
		this.row = row;
		this.line = line;
		this.M = initMat(line, row, rand);
	}
	// Creer une matrice avec des nombres aleatoire
	private static int[][] initMat(int line, int row, int rand)
	{
		int mat[][] = new int [line][row];

		for (int i = 0; i < line; i++)
		{
			for (int j = 0; j < row; j++)
				mat[i][j] = (int)(Math.random() * rand);
		}
		return mat;
	}
	public void setLi(int[] v, int i)
	{
		M[i] = v;
	}
	public int[] getLi(int i)
	{
		return this.M[i];
	}
	public void setv(int v, int i, int j)
	{
		this.M[i][j] = v;
	}
	public int getv(int i, int j)
	{
		return this.M[i][j];
	}
	public int getRow()
	{
		return this.row;
	}
	public int getLine()
	{
		return this.line;
	}
	public int[][] getM()
	{
		return this.M;
	}
	public Matrice gettM()
	{
		int tm[][] = new int [this.row][this.line];

		for (int i = 0; i < this.line; i++)
		{
			for (int j = 0; j < this.row; j++)
				tm[j][i] = M[i][j];
		}
		return new Matrice(tm);
	}
	public String toString()
	{
		String s = new String();

		for (int li[] : this.M)
		{
			s += "(";
			for (int c : li)
				s += " " + c;
			s += " )\n";
		}
		return s;
	}
	public void echo()
	{
		for (int li[] : this.M)
		{
			System.out.print("(");
			for (int c : li)
				System.out.print(" " + c);
			System.out.println(" )");
		}
	}
}
