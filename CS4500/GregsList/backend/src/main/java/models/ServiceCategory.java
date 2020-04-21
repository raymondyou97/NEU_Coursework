package models;

import java.util.ArrayList;
import java.util.List;
import javax.persistence.*;

/**
 * Entity model to represent a mapping of a service category to a record in the
 * database
 */
@Entity
@Table(name = "service_categories")
public class ServiceCategory {
  @Id
  @GeneratedValue(strategy = GenerationType.IDENTITY)
  private Integer id;
  private String title;
  private Integer popularity;
  private String icon;
  private String description;
  @ManyToMany
  @JoinTable(name = "CATEGORIES_SERVICES", joinColumns = @JoinColumn(name = "CATEGORY_ID", referencedColumnName = "ID"), inverseJoinColumns = @JoinColumn(name = "SERVICE_ID", referencedColumnName = "ID"))
  @OrderBy("popularity DESC")
  private List<Service> services = new ArrayList<>();

  public Integer getId() {
    return id;
  }

  public void setId(Integer id) {
    this.id = id;
  }

  public String getTitle() {
    return title;
  }

  public void setTitle(String serviceCategoryName) {
    this.title = serviceCategoryName;
  }

  public List<Service> getServices() {
    return services;
  }

  public void setServices(List<Service> services) {
    this.services = services;
  }

  public String getDescription() {
    return description;
  }

  public void setDescription(String description) {
    this.description = description;
  }

  public Integer getPopularity() {
    return this.popularity;
  }

  public void setPopularity(Integer popularity) {
    this.popularity = popularity;
  }

  public String getIcon() {
    return this.icon;
  }

  public void setIcon(String icon) {
    this.icon = icon;
  }
}