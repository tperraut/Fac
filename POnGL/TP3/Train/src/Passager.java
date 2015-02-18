
public class Passager implements Transportable {
	
	/**
	 * Chaque passager est caractérisé par un nom, et tous les passagers
	 * ont le même poids 75.
	 */
	private static final int POIDS = 75;
	private final String nom;
	
	public Passager(String nom){
		this.nom = nom;
	}
	
	public String getNom(){
		return nom;
	}
	
	public String toString(){
		return nom;
	}

	@Override
	public int getPoids() {
		return POIDS;
	}
	
	static public int getPOIDS(){
		return POIDS;
	}

}
