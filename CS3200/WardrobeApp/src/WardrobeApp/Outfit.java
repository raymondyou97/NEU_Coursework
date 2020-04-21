package WardrobeApp;

import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Types;
import java.util.ArrayList;

//represents an outfit
public class Outfit {
  private int outfitID;
  private Connection connection;

  public Outfit(int outfitID, Connection connection) {
    this.outfitID = outfitID;
    this.connection = connection;
  }

  //returns outfitID
  public int getOutfitID() {
    return this.outfitID;
  }

  //returns outfit description
  public String getDescription() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getOutfitDescription(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.outfitID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //updates outfit description
  public void updateDescription(String description) {
    try {
      String query = "{CALL updateDescription(?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.outfitID);
      stmt.setString(2, description);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //deletes outfit
  public void deleteOutfit(int outfitID) {
    try {
      String query = "{CALL deleteOutfit(?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, outfitID);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //gets number of articles in outfit
  public int getNumberOfArticles() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getNumberOfArticles(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.outfitID);
      stmt.execute();
      result = stmt.getInt(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //gets all articleIDs in outfit
  public ArrayList<Integer> getAllArticleIDs() {
    ArrayList<Integer> intArray = new ArrayList<>();
    try {
      String query = "{CALL getAllArticleIDsInOutfit(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.outfitID);
      rs = stmt.executeQuery();
      while (rs.next()) {
        intArray.add(rs.getInt(1));
      }
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return intArray;
  }

  //prints description of all articles in outfit
  public void printDescriptionOfAllArticles() {
    ArrayList<Integer> articleIDs = this.getAllArticleIDs();
    System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
    for(int i : articleIDs) {
      Article temp = new Article(i, this.connection);
      temp.printAllQualities();
    }
  }

  //prints description of all articles not in outfit
  public void printDescriptionOfAllArticlesNotInOutfit() {
    ArrayList<Integer> intArray = new ArrayList<>();
    try {
      String query = "{CALL getAllArticleIDsNotInOutfit(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.outfitID);
      rs = stmt.executeQuery();
      while(rs.next()) {
        intArray.add(rs.getInt("ArticleID"));
      }
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
    for(int i : intArray) {
      Article temp = new Article(i, this.connection);
      temp.printAllQualities();
    }
  }

  //check if outfit has an articleID
  public boolean hasArticle(int articleID) {
    boolean result = false;
    int temp;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call OutfitHasArticle(?, ?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.outfitID);
      stmt.setInt(3, articleID);
      stmt.execute();
      temp = stmt.getInt(1);
      if(temp == 1) {
        result = true;
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }
}
