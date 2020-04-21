package WardrobeApp;

import java.sql.CallableStatement;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Types;

//represents a piece of article
public class Article {
  private int articleID;
  private Connection connection;

  public Article(int articleID, Connection connection) {
    this.articleID = articleID;
    this.connection = connection;
  }

  //returns articleID
  public int getArticleID() {
    return articleID;
  }

  //returns size
  public String getSize() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleSize(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns color
  public String getColor() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleColor(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns brand
  public String getBrand() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleBrand(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns material
  public String getMaterial() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleMaterial(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns price
  public int getPrice() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticlePrice(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getInt(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns description
  public String getDescription() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleDescription(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns date purchased
  public String getDatePurchased() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleDate(?)}");
      stmt.registerOutParameter(1, Types.VARCHAR);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getString(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns type
  public String getType() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleType(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      int articleType = stmt.getInt(1);
      ArticleType temp = new ArticleType(articleType, this.connection);
      result = temp.getType();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns typeID
  public int getTypeID() {
    int result = 0;
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleType(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      result = stmt.getInt(1);
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //returns type description
  public String getTypeDescription() {
    String result = "";
    try {
      CallableStatement stmt = this.connection.prepareCall("{? = call getArticleType(?)}");
      stmt.registerOutParameter(1, Types.INTEGER);
      stmt.setInt(2, this.articleID);
      stmt.execute();
      int articleType = stmt.getInt(1);
      ArticleType temp = new ArticleType(articleType, this.connection);
      result = temp.getTypeDescription();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
    return result;
  }

  //prints all qualities of the article
  public void printAllQualities() {
    System.out.printf("%-15d%-25s%-40s%-15s%-15s%-15s%-15s%-15d%-40s%-15s\n", this.getArticleID(), this.getType(), this.getTypeDescription(),
            this.getSize(), this.getColor(), this.getBrand(), this.getMaterial(), this.getPrice(), this.getDescription(), this.getDatePurchased());
  }

  //updates values for qualities
  public void updateQualities(String type, String size, String color, String brand, String material, int price, String description, String datePurchased) {
    try {
      String typeDescription = "a " + type + " article";
      String query = "{CALL UpdateTypeFirst(?, ?, ?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setString(1, type);
      stmt.setString(2, typeDescription);
      stmt.setInt(3, this.getTypeID());
      stmt.executeQuery();


      String query2 = "{CALL UpdateOutfitArticle(?, ?, ?, ?, ?, ?, ?, ?)}";
      CallableStatement stmt2 = this.connection.prepareCall(query2);
      stmt2.setString(1, size);
      stmt2.setString(2, color);
      stmt2.setString(3, brand);
      stmt2.setString(4, material);
      stmt2.setInt(5, price);
      stmt2.setString(6, description);
      stmt2.setString(7, datePurchased);
      stmt2.setInt(8, this.articleID);
      stmt2.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

  //deletes article
  public void deleteArticle(int articleID) {
    try {
      String query = "{CALL deleteArticle(?)}";
      CallableStatement stmt = this.connection.prepareCall(query);
      stmt.setInt(1, articleID);
      stmt.executeQuery();
    } catch (SQLException e) {
      System.out.println(e.getMessage());
    }
  }

}
