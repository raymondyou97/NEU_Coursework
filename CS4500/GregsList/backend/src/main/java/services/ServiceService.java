package services;

import models.ServiceQuestion;
import repositories.ServiceQuestionRepository;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.ArrayList;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;

import models.Service;
import models.ServiceCategory;
import models.User;
import repositories.ServiceCategoryRepository;
import repositories.ServiceRepository;
import repositories.UserRepository;

@RestController

@CrossOrigin(origins = "*")
public class ServiceService {
    @Autowired
    ServiceRepository serviceRepository;
    @Autowired
    ServiceCategoryRepository serviceCategoryRepository;
    @Autowired
    UserRepository userRepository;
    @Autowired
    ServiceQuestionRepository serviceQuestionRepository;

    @GetMapping("/api/services")
    public List<Service> findAllService() {
        return serviceRepository.findAllServices();
    }

    @GetMapping("/api/services/{serviceId}")
    public Service findServiceById(@PathVariable("serviceId") Integer id) {
        return serviceRepository.findServiceById(id);
    }

    @PostMapping("/api/services")
    public Service createService(@RequestBody Service service) {
        return serviceRepository.save(service);
    }

    @PutMapping("/api/services/{serviceId}")
    public Service updateService(@PathVariable("serviceId") Integer id, @RequestBody Service serviceUpdates) {
        Service service = serviceRepository.findServiceById(id);
        service.setTitle(serviceUpdates.getTitle());
        return serviceRepository.save(service);
    }

    @DeleteMapping("/api/services/{serviceId}")
    public void deleteService(@PathVariable("serviceId") Integer id) {
        serviceRepository.deleteById(id);
    }

    @PostMapping("/api/services/{serviceId}/categories/{categoryId}")
    public Service addCategory(@PathVariable("serviceId") Integer serviceId,
            @PathVariable("categoryId") Integer categoryId) {
        ServiceCategory serviceCategory = serviceCategoryRepository.findServiceCategoryById(categoryId);
        Service service = serviceRepository.findServiceById(serviceId);
        List<Service> categoryRelations = serviceCategory.getServices();
        List<ServiceCategory> serviceRelations = service.getServiceCategories();
        if (!serviceRelations.contains(serviceCategory)) {
            categoryRelations.add(service);
            serviceCategory.setServices(categoryRelations);
            serviceRelations.add(serviceCategory);
            service.setServiceCategories(serviceRelations);
        }
        serviceCategoryRepository.save(serviceCategory);
        return serviceRepository.save(service);
    }

    @GetMapping("/api/services/{serviceId}/categories")
    public List<ServiceCategory> getServiceCategories(@PathVariable("serviceId") Integer serviceId) {
        Service service = serviceRepository.findServiceById(serviceId);
        return service.getServiceCategories();
    }

    @DeleteMapping("/api/services/{serviceId}/users/{userId}")
    public User removeProvider(@PathVariable("serviceId") Integer serviceId, @PathVariable("userId") Integer userId) {
        Service service = serviceRepository.findServiceById(serviceId);
        User user = userRepository.findUserById(userId);
        List<User> providers = service.getProviders();
        List<Service> services = user.getServices();
        if (providers.contains(user)) {
            services.remove(service);
            user.setServices(services);
            providers.remove(user);
            service.setProviders(providers);
        }
        serviceRepository.save(service);
        return userRepository.save(user);
    }

    @PostMapping("/api/services/{serviceId}/users/{userId}")
    public User addProvider(@PathVariable("serviceId") Integer serviceId, @PathVariable("userId") Integer userId) {
        Service service = serviceRepository.findServiceById(serviceId);
        User user = userRepository.findUserById(userId);
        List<User> providers = service.getProviders();
        List<Service> services = user.getServices();
        if (!providers.contains(user)) {
            providers.add(user);
            service.setProviders(providers);
            services.add(service);
            user.setServices(services);
        }
        serviceRepository.save(service);
        return userRepository.save(user);
    }

    @GetMapping("/api/services/{serviceId}/users")
    public List<User> getProviders(@PathVariable("serviceId") Integer serviceId) {
        Service service = serviceRepository.findServiceById(serviceId);
        return service.getProviders();
    }

    @PostMapping("/api/services/{serviceId}/questions/{questionId}")
    public ServiceQuestion addServiceQuestion(@PathVariable("serviceId") Integer serviceId,
            @PathVariable("questionId") Integer questionId) {
        Service service = serviceRepository.findServiceById(serviceId);
        ServiceQuestion sq = serviceQuestionRepository.findServiceQuestionById(questionId);
        List<ServiceQuestion> questions = service.getServiceQuestions();

        if (!questions.contains(sq)) {
            questions.add(sq);
            service.setServiceQuestions(questions);
            sq.setService(service);
        }

        serviceRepository.save(service);
        return serviceQuestionRepository.save(sq);
    }

    @GetMapping("api/services/{serviceId}/questions")
    public List<ServiceQuestion> findAllServiceQuestionsForService(@PathVariable("serviceId") Integer serviceId) {
        return serviceQuestionRepository.findAllServiceQuestionsForService(serviceId);
    }

    @RequestMapping(value = "/api/services/query", method = RequestMethod.GET)
    public List<User> searchForProviderByService(@RequestParam("term") String searchTerm,
            @RequestParam("zip") Integer zipCode) {
        ArrayList<User> providers = new ArrayList<>();
        List<Service> matches = serviceRepository.findServicesByTitle(searchTerm);
        if (matches.isEmpty()) {
            User match = userRepository.findByUsername(searchTerm);
            if (match != null) {
                providers.add(match);
            }
            return providers;
        }
        for (Service service : matches) {
            providers.addAll(service.getProviders());
        }
        Collections.sort(providers, Comparator.comparing(user -> user.calculateDistance(zipCode)));
        return providers;
    }

}
