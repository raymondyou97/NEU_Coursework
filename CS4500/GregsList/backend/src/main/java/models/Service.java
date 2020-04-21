package models;

import java.util.List;

import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.persistence.Id;
import javax.persistence.JoinColumn;
import javax.persistence.JoinTable;
import javax.persistence.ManyToMany;
import javax.persistence.OneToMany;
import javax.persistence.Table;

import com.fasterxml.jackson.annotation.JsonIgnore;

@Entity
@Table(name = "services")
public class Service {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Integer id;
    private String title;
    private Integer popularity;
    @ManyToMany
    @JsonIgnore
    @JoinTable(name = "PROVIDERS_SERVICES", joinColumns = @JoinColumn(name = "SERVICE_ID", referencedColumnName = "ID"), inverseJoinColumns = @JoinColumn(name = "USER_ID", referencedColumnName = "ID"))
    private List<User> providers;
    @ManyToMany(mappedBy = "services")
    @JsonIgnore
    private List<ServiceCategory> serviceCategories;
    @OneToMany(mappedBy = "service")
    private List<ServiceQuestion> serviceQuestions;

    public Service() {
    }

    public Service(Integer id, String title, Integer popularity, List<User> providers,
            List<ServiceCategory> serviceCategories) {
        this.id = id;
        this.title = title;
        this.popularity = popularity;
        this.providers = providers;
        this.serviceCategories = serviceCategories;
    }

    public List<ServiceCategory> getServiceCategories() {
        return serviceCategories;
    }

    public void setServiceCategories(List<ServiceCategory> serviceCategories) {
        this.serviceCategories = serviceCategories;
    }

    public List<User> getProviders() {
        return providers;
    }

    public void setProviders(List<User> providers) {
        this.providers = providers;
    }

    public Integer getId() {
        return id;
    }

    public void setId(Integer id) {
        this.id = id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public Integer getPopularity() {
        return popularity;
    }

    public void setPopularity(Integer popularity) {
        this.popularity = popularity;
    }

    public List<ServiceQuestion> getServiceQuestions() {
        return serviceQuestions;
    }

    public void setServiceQuestions(List<ServiceQuestion> serviceQuestions) {
        this.serviceQuestions = serviceQuestions;
    }

    public void addCategory(ServiceCategory category) {
        this.serviceCategories.add(category);
    }

    public void deleteCategory(Integer categoryId) {
        for (int i = 0; i < this.serviceCategories.size(); i++) {
            if (this.serviceCategories.get(i).getId().equals(categoryId)) {
                this.serviceCategories.remove(i);
            }
        }
    }
}