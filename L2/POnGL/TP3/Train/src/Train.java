import java.util.ArrayList;

/**
 * Classe des trains.
 */
public class Train
{

	/**
	 * L'état d'un train est caractérisé par une liste d'éléments de train.
	 */
	private ArrayList<EltTrain> elements;

	/**
	 * À l'origine, un train ne contient aucun élément.
	 */
	public Train()
	{
		elements = new ArrayList<EltTrain>();
	}

	/**
	 * Ajout d'un élément au train.
	 * @param elt  l'élément à ajouter.
	 */
	public void ajouterElt(EltTrain elt)
	{
		this.elements.add(elt);
	}

	/**
	 * Calcul du poids total du train et de son chargement.
	 * @return  le poids total.
	 */
	public int getPoids()
	{
		int poids = 0;
		for (EltTrain e : elements)
			poids += e.getPoids();
		return (poids);
	}

	/**
	 * Calcul de la capacité de traction de l'ensemble des éléments
	 * moteurs du train.
	 * @return  la capacité de traction totale.
	 */
	public int getTractionMax()
	{
		int tractionMax = 0;
		for (EltTrain e : elements)
		{
			if (e instanceof Locomotive)
				tractionMax += ((Locomotive)e).getTractionMax();
			else if (e instanceof Autorail)
				tractionMax += ((Autorail)e).getTractionMax();
		}
		return (tractionMax);
	}

	/**
	 * Vérification de la bonne formation du train.
	 * @return  true si et seulement si le train est bien formé.
	 */
	public boolean bienForme()
	{
		boolean devant = true;
		for (EltTrain e : elements)
		{
			if (e instanceof Autorail)
			{
				if (((Autorail)e).placesRestantes() < 0
						|| ((Autorail)e).placesRestantes()
							> ((Autorail)e).getCapacite()
						|| !devant)
					return (false);
			}
			if (e instanceof Wagon)
			{
				if (((Wagon)e).placesRestantes() < 0
						|| ((Wagon)e).placesRestantes()
							> ((Wagon)e).getCapacite())
					return (false);
				devant = false;
			}
			if (e instanceof PorteConteneurs)
			{
				if (((PorteConteneurs)e).calculerVolume() < 0
						|| ((PorteConteneurs)e).calculerVolume()
							> ((PorteConteneurs)e).getCapacite())
					return (false);
				devant = false;
			}
			if (e instanceof PorteVoitures)
			{
				if (((PorteVoitures)e).calculerVolume() < 0
						|| ((PorteVoitures)e).calculerVolume()
							> ((PorteVoitures)e).getCapacite())
					return (false);
				devant = false;
			}
			if (e instanceof Locomotive && !devant)
				return (false);
		}
		if (this.getPoids() > this.getTractionMax())
			return (false);
		return (true);
	}


	/**
	 * Calcul du nombre total de places restantes dans les wagons et
	 * autorail de notre train.
	 * @return  le nombre de places restantes.
	 */
	public int placesRestantes(){
		int placesRestantes = 0;
		for(EltTrain elt : elements){
			if(elt instanceof Wagon)
				placesRestantes += ((Wagon) elt).placesRestantes();
			else if (elt instanceof Autorail)
				placesRestantes += ((Autorail) elt).placesRestantes();
		}
		return placesRestantes;
	}

}
