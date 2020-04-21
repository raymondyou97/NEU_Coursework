package WardrobeApp;

import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Types;
import java.util.HashSet;

//represents a user
public class User {
  private int userID;
  private Connection connection;


  public User(int userID, Connection connection) {
    this.userID = userID;
    this.connection = connection;
  }

  public int getUserID() {
    return userID;
  }

  //prints number of outfits for current user
  public void printNumberOfOutfits() {
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getNumOutfits(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.userID);
      stmt.execute();
      int result = stmt.getInt(1);
      System.out.println(this.userID + " has " + result + " outfits.");

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //gets number of outfits for current user
  public int getNumberOfOutfits() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getNumOutfits(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getInt(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //gets number of articles for current user
  public int getNumberOfArticles() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getNumberOfArticlesForUser(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getInt(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //check if user has that outfitID
  public boolean hasOutfitID(int outfitID) {
    try {
      String query = "{CALL getOutfitIDs(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.userID);
      rs = stmt.executeQuery();

      while (rs.next()) {
        if(rs.getInt(1) == outfitID) {
          return true;
        }
      }

    } catch (SQLException e) {
      e.getMessage();
    }
    return false;
  }

  //check if user has that articleID
  public boolean hasArticleID(int articleID) {
    boolean check = false;
    try {
      String query = "{CALL getArticleIDs(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.userID);
      rs = stmt.executeQuery();
      while (rs.next()) {
        if(rs.getInt(1) == articleID) {
          check = true;
        }
      }

    } catch (SQLException e) {
      e.getMessage();
    }
    return check;
  }

  //prints out information for each outfit of user
  public void printOutfits() {
    try {
      String query = "{CALL getOutfitIDs(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.userID);
      rs = stmt.executeQuery();
      HashSet<Integer> outfitIDs = new HashSet<>();
      while (rs.next()) {
        outfitIDs.add(rs.getInt(1));
      }
      System.out.printf("%-15s%-30s%-15s\n", "Outfit ID", "Outfit Description", "# of Articles");
      for(int temp : outfitIDs) {
        Outfit tempOutfit = new Outfit(temp, this.connection);
        System.out.printf("%-15d%-30s%-15d\n", tempOutfit.getOutfitID(), tempOutfit.getDescription(), tempOutfit.getNumberOfArticles());
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //prints out information for each article of user
  public void printArticles() {
    try {
      String query = "{CALL getArticleIDs(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, this.userID);
      rs = stmt.executeQuery();
      HashSet<Integer> articleIDs = new HashSet<>();
      while (rs.next()) {
        articleIDs.add(rs.getInt(1));
      }
      System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
      for(int temp : articleIDs) {
        Article tempArticle = new Article(temp, this.connection);
        tempArticle.printAllQualities();
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //returns username
  public String getUsername() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getUsername(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getString(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns full name
  public String getFullName() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getFullName(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getString(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns age
  public int getAge() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getAge(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getInt(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns gender
  public String getGender() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getGender(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getString(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns email address
  public String getEmailAddress() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getEmailAddress(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.userID);
      stmt.execute();
      result = stmt.getString(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns the typeID from given type
  public int getTypeIDFromDescription(String type) {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getTypeIDFromDescription(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setString(2, type);
      stmt.execute();
      result = stmt.getInt(1);

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //prints the information of user
  public void printUserInformation() {
    System.out.println("===================================================================================================================================" +
            "===========================================================================================================================");
    System.out.println("Here is your user information: ");
    System.out.printf("%-15s%-25s%-20s%-30s%-15s%-15s%-30s\n", "UserID", "Username", "Password", "Full Name", "Age", "Gender", "Email Address");
    System.out.printf("%-15d%-25s%-20s%-30s%-15d%-15s%-30s\n", getUserID(), getUsername(), "*************", getFullName(), getAge(), getGender(), getEmailAddress());
  }


  //Search query methods for size, color, brand, material
  public void searchWithColumnAndValueString(String column, String value) {
    try {
      //insert column name and column value. Wasn't possible to do this with a procedure as MySQL didn't accept column names as inputs
      PreparedStatement statement = this.connection.prepareStatement("SELECT ArticleID FROM OutfitArticle where " + column + " = ? and UserID = ?");
      statement.setString(1, value);
      statement.setInt(2, this.userID);
      ResultSet resultSet = statement.executeQuery();
      HashSet<Integer> articleIDs = new HashSet<>();
      while (resultSet.next()) {
        articleIDs.add(resultSet.getInt("ArticleID"));
      }
      if(articleIDs.size() == 0) {
        System.out.println("You have no articles where " + column + " = " + value);
      }
      else {
        System.out.println("Here are your articles with " + column + " = " + value);
        System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
        for(int temp : articleIDs) {
          Article tempArticle = new Article(temp, this.connection);
          tempArticle.printAllQualities();
        }
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //Search query method for type
  public void searchWithColumnAndValueType(String typeDescription) {
    try {
      int temp = getTypeIDFromDescription(typeDescription);
      String query = "{CALL getArticleIDsWithTypeID(?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, temp);
      rs = stmt.executeQuery();
      HashSet<Integer> articleIDs = new HashSet<>();
      while (rs.next()) {
        articleIDs.add(rs.getInt("ArticleID"));
      }
      if(articleIDs.size() == 0) {
        System.out.println("You have no articles where article type " + " = " + typeDescription);
      }
      else {
        System.out.println("Here are your articles with ArticleType = " + typeDescription);
        System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
        for(int temp1 : articleIDs) {
          Article tempArticle = new Article(temp1, this.connection);
          tempArticle.printAllQualities();
        }
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //Search query method for price range
  public void searchWithLowerAndUpper(int lowerBound, int upperBound) {
    try {
      String query = "{CALL getArticleIDPriceRange(?, ?)}";
      ResultSet rs;
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, lowerBound);
      stmt.setInt(2, upperBound);
      rs = stmt.executeQuery();
      HashSet<Integer> articleIDs = new HashSet<>();
      while (rs.next()) {
        articleIDs.add(rs.getInt("ArticleID"));
      }
      if(articleIDs.size() == 0) {
        System.out.println("You have no articles where the price of article type is between " + lowerBound + " and " + upperBound + " inclusive");
      }
      else {
        System.out.println("Here are your articles with price inclusively between " + lowerBound + " and " + upperBound);
        System.out.printf("%-15s%-25s%-40s%-15s%-15s%-15s%-15s%-15s%-40s%-15s\n", "ArticleID", "Type", "Type Description", "Size", "Color", "Brand", "Material", "Price", "Description", "Date Purchased");
        for(int temp1 : articleIDs) {
          Article tempArticle = new Article(temp1, this.connection);
          tempArticle.printAllQualities();
        }
      }

    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }
}
